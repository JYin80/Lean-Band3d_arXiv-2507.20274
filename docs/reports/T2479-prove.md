Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 23:29:09 UTC 2026

Scope: the pin `STCltFargL d` (`Chain/CltGen.lean:167`) for every `d`, `HCltOf` + `STReg5I` + `STThPropsg` + `STKpropsg` + `STExpInvgL` => `STCltFarConclgL`; band producers (target 7); band bridge (target 8). Route = band `stCltFar_holds` (`Evolution/CltFar.lean:1757`): mean part at `tau/2` (`meanFar_eventually`), window fluctuation `cltFar_fluc` at `(tau/2, D+3)`, off-window `cltFar_off` at `(D0, D+1)`, deterministic split `cltFar_far_le`, union bound over `{sigma | sigma 0 != sigma 1} x (Fin 2 -> Z_L^d)`.

### (i) Exponent table (instance: d=3, szCL `L=2m^5, W=2^m, m=n+24`, lam=1, c=1/6, dd=1/10, kappa=1/2, delta=1/10, s=0, t=1-L^-2, tau=1/2, D=1; `Step5Pins.lean:642-717`, `CltGood.lean:1002`)
| quantity | value | constraint | slack |
|---|---|---|---|
| mean / fluc exponents | `tau/2` each (`CltFar.lean:1776-1781`) | `N^{tau/2} N^{tau/2} = N^tau` | 0 (equality) |
| `Nh = N^{tau/2}` | `N^{1/4}`; need `N >= 3^{2/tau}` | `cltFar_far_le`: `2 Nh z + z <= Nh^2 z` iff `Nh^2-2Nh-1 >= 0` (root `1+sqrt2 = 2.4142`), hyp `Nh >= 3` | 2 at `Nh=3` |
| `D0 = 6d/5+(d-2)/c+1` | `53/5 = 10.6` (d=3, c=1/6) | `W^{-D0} <= zeta = A^{-6/5}/(R^{d-2}+1)`: `A <= dd^-2 W^d`, `R <= L <= N <= W^{1/c}` | needs `W >= 2(dd^-2)^{6/5} = 502.4`; `W=1.68e7` at n=0 |
| fluc call `(tau_f, D_f) = (tau/2, D+3)` | `(1/4, 4)` | `p = ceil((D_f+2)/tau_f)`, `p tau_f >= D_f+2` | `p=24`, 6 >= 6: 0 |
| `m3`, `m1` (`CltFar.lean:1524-1529`) | `6p+ceil(D_f)+3 = 151`; `18p+ceil(D_f)+4 = 440` | `hm3`, `hD1` | 0, 0 |
| off call `(D0, D+1)` | prob `N^{-(D+1)}` | `D0 > 0` (`hD0`) | 10.6 |
| union (`cltFar_union_numeric`) | `N^{-(D+1)} + c N^{-(D+3)} <= N^{-D}`, `c <= 4N^2`, `N >= 5` | ratio `= 5/N` | 0 at `N=5`; `2.6e-43` at n=0 |
| index count | `2 L^{2d}` | `<= 4 N^2` (`cltFar_card_pair_le`) | factor `2 W^6` |
| regime `STReg5I` | `lam^2/L^2 <= 1-t <= 1-s <= lam^2`, i.e. `L^-2 <= L^-2`, `1 <= 1` | `Step5Pins.lean:44` | 0, 0 (equality at the instance) |
| `N^{-1+delta} <= 1-t` (`HCltOf`) | `delta=1/10` | `-0.9 log N <= -2 log L` | `-89.7 <= -33.2` |
| spectral: `kappa <= Im m`, `kappa' = min(kappa,1/2)` | `Im mE(1/2) = sqrt15/4 = 0.9682`; `kappa'=1/2` | `kappa <= Im m` (`HCltOf`); `\|E\| = 1/2 <= 2-kappa` (band target 7 only) | 0.468; 1 |
| `Admissible c=1/6, dd=1/10` | `N <= W^6` iff `L <= W`; `W^{-3/2+dd} <= lam <= dd^-1` | `Defs/Sizes.lean:164-178` | `L/W = 0.949`; `W^{-1.4} <= 1 <= 10` |
| `Theta` constants at `c=1/2` | `C6 = C1 2^{d-1} = 4 C1`; `C7 = C2 3^d 2^d = 216 C2`; `C5` = `Prop5Decay` | `prop6Diff1_holds`, `prop7Diff2_holds` (`Prop6Hold.lean:353,384`), `Prop5Decay` (`Pins.lean:34`); `0 < g <= Lambda = dd^-1`, `kappa' <= Im m` | `mSigma E s = PropSpin (mE E) s` (`Semicircle.lean:85`, `Pins.lean:30`) |
| decay exponents (`STThPropsg`) | `Bparam` `(K+1)^{-(d-2)}`; BD1 `(\|a\|+1)^{-(d-1)}`; BD2 `(\|a\|+1)^{-d}`; weights `\|a-b\|^{-(d-2)}`, `\|a2-b1\|^{-(d-1)}` (`CltGen.lean:127-138`) | same shapes as `Prop5Decay` (`Pins.lean:34-42`), `Prop6Diff1` (`:57-67`) and `prop7Diff2_holds` (`Prop6Hold.lean:395-398`) | exact match, no loss |
| `K` bound | `\|\|K\|\| <= c1/A`, `c1 = C5 (1+2^{d-1})` | `cltFar_Theta_sup` (`CltFar.lean:456`): `\|Theta\| <= C5(1+2^{d-1})/g^2` under `g^2/L^2 <= 1-u` (= `STReg5I`); `K = W^{-d} Theta` per the `STKpropsg` docstring | `A = g^2 W^d` exact |
| explicit eventual thresholds | `c log N >= 40` (n>=59), `2d <= c log N` (n>=0), `N>=5`, `N^{tau/2}>=3`, `W>=502.4` (n>=0) | conclusion is `forall^f n`; the others (`4 Kp M log^{24p} <= N^2`, `(4(C5(1+2^{d-1}))^2)^{2p} <= N`, ...) contain existential `M, C5` | no numeric value; not hypotheses |
| line budget (below) | central 546 / 637 / 958, total 2141 | stop line 2000 per file; X1b-C1 3000; split trigger 1950; reserve line 1800 | 1454 / 1363 / 1042 per file; 859 total; split triggered (2141 > 1950) |

### (ii) One nondegenerate instance (`d=3`, `n=0`; every hypothesis of `STCltFargL` that is deterministic holds at all `n`)
Hypotheses at the instance: `HCltOf` with `(kappa,delta,c,dd,Cd) = (1/2,1/10,1/6,1/10,1)` is `cltGood_hCltOf_szCL` (`CltGood.lean:1002`); its only open inputs are the Step-2 pins `STLocalEntryUgL`, `STGdecayWgL` (other gate, hypotheses of the instance); `STReg5I`: regime row; `STThPropsg`, `STKpropsg`: band target 7 (`Theta` constants, decay exponents and `K` bound rows); `STExpInvgL`: `stExpInvgL_band`. Index set nonempty at every `n` (`szCL_cltFar_index_nonempty`, `Step5Pins.lean:900`): `sigma=(+,-)`, `a=(x_n,0)`, `|a1-a2| = m^5 = L/2`; rows below. `p, m3, m1` are the values the proof of `cltFar_fluc` takes at `(tau/2, D+3)`.
Command: `python3 -I scratchpad/T2479/inst.py` (floats via `math.log`; equalities in `Fraction`/`int`):
```
n=0: L=15925248 W=16777216 log10 N=43.28
Admissible: N^(1/6) <= W  (N <= W^6, i.e. L <= W)          OK  L/W=0.949
WO: W^(-3/2+1/10) <= lam=1 <= 1/dd=10                      OK  
0 <= s < t < 1                                             OK  
STReg5I: lam^2/L^2 <= 1-t  (equality)                      OK  slack 0
STReg5I: 1-s <= lam^2  (equality)                          OK  slack 0
N^(-1+delta) <= 1-t = L^-2  (log form)                     OK  -89.7 <= -33.2
kappa=1/2 <= Im mE(1/2) = sqrt(15)/4                       OK  0.9682
|E|=1/2 <= 2-kappa=3/2                                     OK  
A=lam^2 W^3 in [1, dd^-2 W^3]                              OK  
--- exponents at tau=1/2, D=1 (pin), fluc called at (tau/2, D+3)
p=ceil((Df+2)/tf)                                          OK  tf=1/4 Df=4 p=24
p*tf >= Df+2                                               OK  6 >= 6 slack 0
m3 >= 6p+Df+3                                              OK  m3=151 slack 0
m1 >= 18p+Df+4                                             OK  m1=440 slack 0
D0=6d/5+(d-2)/c+1 > 0                                      OK  D0=53/5=10.6
hbig: W >= 2*(dd^-2)^(6/5)                                 OK  threshold 502.4, W=16777216
N^(tau/2) >= 3 (Nh>=3)                                     OK  N^(1/4)=10^10.8
Nh^2-2Nh-1>=0 at Nh=3                                      OK  slack 2; root 1+sqrt2=2.4142
N >= 5                                                     OK  
card(sigma,a) <= 4N^2                                      OK  card=3.262e+43 4N^2=1.455e+87
N^-(D+1)+c N^-(D+3) <= N^-D for c=4N^2                     OK  ratio=5/N=2.62e-43; needs N>=5
eventual (not a hypothesis; n0 below): c*log N = 16.6 at n=0, needs >= 40
--- index set (n=0): ell_s=min(max(1/sqrt|1-s|,1),L)=1, ell_t=min(max(L,1),L)=L
(log W)^5*ell_s <= ell_t                                   OK  1274041 <= 15925248
|a1-a2|=m^5=L/2 <= 1/2 (logW)^1.5 ell_t+(logW)^2.5 ell_s   OK  7962624 <= 540271639
--- propagator constants at c=1/2, d=3 (prop6Diff1: C1*(1-c)^-(d-1); prop7Diff2: C2*3^d*(1-c)^-d)
factors: BD1 x4 (C1), BD2 x216 (C2); mean: A^-6/5 / (R^1+1); weights a1: |a|^-1, a2: |a|^-2
--- eventual-in-n thresholds at szCL (explicit ones only; M, C5, Cd, c1 are existential)
n0: c logN>=40 at n=59 (logN=241.0); c logN>=2d at n=0; N>=5 at n=0; N^(1/4)>=3 at n=0; W>=502.4 at n=0
tau=1/10: N^(1/20)>=3 first at n=0 (logN=99.7)
Admissible & N^(-0.9)<=L^-2 for n=0..2000: True
ALL OK
```
External-hypothesis limit check (TEAM 8 lesson 14; the pin's inputs `Admissible`, `STReg5I`, `N^{-1+delta} <= 1-t` are hypotheses, the thresholds are in the conclusion): `N^{1/6} <= W` iff `L <= W`, `L/W = (2 m^5)/2^m -> 0`; `log N = 3 (m ln2 + ln(2 m^5)) -> inf` (`SizeTendsto`); `N^{-0.9} <= L^-2` in log form `-0.9 log N <= -2 log L`, true for n=0..2000 (last line above); `c log N >= 40` first true at `n=59`.

### Central line estimate per file (X1b-C1, X1b-C2)
Source counts (declaration spans, `scratchpad/T2479/decls.py`; band-token regex of T2455-prove line 191; instance sections excluded):
```
CltMoments1 file 2133 pre-instance decl lines 1866 band-touching 403 non-band 1463
CltMoments2 file 1707 pre-instance decl lines 1135 band-touching 587 non-band 548
MeanFar file 2312 pre-instance decl lines 2069 band-touching 796 non-band 1273
CltFar file 1959 pre-instance decl lines 1798 band-touching 971 non-band 827
```
Estimate (`scratchpad/T2479/est.py`): `lines = 40 (header) + restated band-touching lines x (1-reuse) + new text`; restated = band-touching spans feeding the file (`CltMoments1:904-1031` + `CltMoments2:78-225, 783-1208` -> `CltMoments2G`; `MeanFar:839-1111, 1248-1915, 1954-2137` -> `MeanFarG`; `CltFar:69-104, 308-1857` -> `CltFarG`); reuse 0.25 central (ticket's "about a quarter by name / `open private`"), 0.40 low, 0 high; new text = `CltMoments2G` 70 (`lenv_of_rep` and weight glue), `CltFarG` 92 (target 7: 1.5 x the 61 lines of the band analogs `cltFar_Theta_shift, _H5_at, _mE_im_ge, _K_le, _K_le', meanFar_K_eq`) + 60 (target 8) + 60 (instances). Header 40, the 60s and the factor 1.5 are my assumptions, not measurements.
```
restated band-touching lines: CltMoments2G 582  MeanFarG 796  CltFarG 942
target-7 analog lengths sum 61 -> x1.5 = 92
CltMoments2G  low(reuse .40)   459  central(reuse .25)   546  high(reuse 0)   692
MeanFarG      low(reuse .40)   518  central(reuse .25)   637  high(reuse 0)   836
CltFarG       low(reuse .40)   817  central(reuse .25)   958  high(reuse 0)  1194
TOTAL low 1794 central 2141 high 2722   (X1b-C1 line 3000; split trigger 1950; reserve line 1800 per file)
```
Central total 2141 <= 3000: X1b-C1 not triggered (high case 2722 also <= 3000; ticket's 2.6k reference also below). Central 2141 > 1950: the pre-signed split applies: X1b-1 = `CltMoments2G` (546) + `MeanFarG` (637) = 1183; X1b-2 = `CltFarG` (958). No file is predicted above 1800 (largest high case 1194), so the reserve is not needed; `Evolution/CltFarG2.lean` stays named as reserve (ticket), used only if `CltFarG` is later predicted above 1800 (targets 7-9 move there). The ticket's own central is 600 / 500 / 900 = 2000, mine 546 / 637 / 958 = 2141. The `MeanFarG` excess (+137) is from the band-touching private declarations `meanFar_n_kernel` (140 lines) and `meanFar_at_n` (236 lines) in `MeanFar` section 6, which have to be restated (their lines are in the 796).

### Verdict per target
1 weights `cltMom1_weight_a1g/_a2g`: PASS (conjuncts 1, 3, 4 of `STThPropsg` + `meanFar_T1`; exponents `d-2`, `d-1` match).
2 vocabulary `CltMom2.Zg ...`: PASS (definitions only).
3 moment layer: PASS (`p, m3, m1` rows, `hD1`, `hm3` at slack 0 are inequalities the proof chooses `p` to meet; no new exponent).
4 mean part `meanFar_eventuallyg`: PASS (`STKpropsg` conj 1-2, `STThPropsg` conj 3, 5, `STExpInvgL`; `STReg5I` supplies `g^2/L^2 <= 1-u`).
5 far steps: PASS (D0, `(tau/2, D+3)` rows).
6 pin `stCltFargL_holds`: PASS (union row: slack 0 at `N=5`, eventual in `n`).
7 band producers: PASS (`Prop5Decay`, `prop6Diff1_holds`, `prop7Diff2_holds` at `Lambda=dd^-1`, `c=1/2`, `kappa'`; `K` bound from `STReg5I`).
8 bridge `stCltFar_of_gL`: PASS; 9 instance: PASS (`Admissible`, regime and index-set rows, `cltGood_hCltOf_szCL`).
Line estimate: central 2141 <= 3000, no BLOCKED; split X1b-1 / X1b-2; reserve `CltFarG2` named, unneeded.
Overall: PASS.
### (a′) Preflight additions — Tue Oct 13 00:18:19 UTC 2026
No verdict of (a) changes. (a) gives (i), (ii) and the line estimate; the ticket's (iii) reuse table, (iv) hypothesis table and (vi) name-clash grep are not in it (CLAUDE.md §4 step 1 caps (a) at (i)-(ii)); they are in (b), written from the compiled text. This 1b run delivers **X1b-1** of the pre-signed split that (a) selects (central 2141 > 1950): targets 1-4 in `CltMoments2G`, `MeanFarG`. Targets 5-9 (`CltFarG`: dom/off/fluc steps, `stCltFargL_holds`, band producers `bandFM_STThPropsg`/`bandFM_STKpropsg`, bridge `stCltFar_of_gL`) are X1b-2 on `t/T2479b`; none of them is a target of this branch (private copies of the statements of 7a, 7b serve its instances, note 7).
## (b) Script output — Tue Oct 13 00:18:19 UTC 2026
Scratch scripts in `scratchpad/T2479/`: `stmts.py`, `examples.py`, `gtab.py`, `diffcheck.py`, `mkreport.py`. Commits on `t/T2479` (`git log main..t/T2479`): `a8c9aaa5` CltMoments2G, `524681ed` MeanFarG with registry and root imports, `c30e4483` docstrings, `83c1a06f` the `T2479_MeanFarg` example, `306e4bba` instances close `STThPropsg`, `STKpropsg`, `03f828ee` `change` for `show`. Order as the ticket asks: layout (b1), tables (b2, b3), statements (b4), greps (b5), registry (b6), instances (b7); then builds, name clash, tripwire, narrative.
**b1. Layout, line counts against the stop line 2,000, imports, G1**
```
$ git rev-parse --short HEAD; wc -l <2 new files>; git diff main...t/T2479 --name-only; grep -n "^import" <2 new files>; git diff main...t/T2479 -- <4 band files> RBM3D/Chain RBM3D/Induction RBM3D/BA | wc -l
03f828ee
     729 RBM3D/Evolution/CltMoments2G.lean
     869 RBM3D/Evolution/MeanFarG.lean
    1598 total
RBM3D.lean
RBM3D/Evolution/CltMoments2G.lean
RBM3D/Evolution/MeanFarG.lean
RBM3D/Test/Axioms.lean
RBM3D/Evolution/CltMoments2G.lean:6:import RBM3D.Evolution.CltMoments2
RBM3D/Evolution/CltMoments2G.lean:7:import RBM3D.Chain.CltGen
RBM3D/Evolution/MeanFarG.lean:6:import RBM3D.Evolution.MeanFar
RBM3D/Evolution/MeanFarG.lean:7:import RBM3D.Chain.CltGen
       0
```
**b2. Reuse table (iii)** (band declaration of the four files -> use in X1b-1)
- By name (public, model-free): `CltMom1.uw/G/cs/Cd`, `cltMom1_scale_bd1/_scale_comparable/_zdistInf_sub_comm`; `CltMom2.X`, `cltMom2_moment_le :628`, `_markov :747`, `_hzu :1090`; `meanFar_core :666`, `_T1 :762`, `_T2 :814`, `_Cd :473`.
- `open private` (20): CltMoments1 `cltMom1_pow_add_one_ge :91`; CltMoments2 `cltMom2_sum_pair :834`, `_eta :839`, `_weight_algebra :854`; MeanFar `meanFar_norm_integral_le :845`, `_zdistInf_le`, `_zdistInf_neg`, `_ell_sq :1255`, `_c3 :1294`, `_c0 :1297`, `_c3_pos :1299`, `_BctlSTWB :1303`, `_Cd_nonneg :1116`, `_numeric_main :1123`, `_tiny :1510`, `_eta_bound :1624`, `_eps_bound :1654`, `_pureN :1938`, `_inv_pow_eq :1959`, `_three_halves :1964`.
- Restated over `(C, μ)`: CltMoments1 `cltMom1_weight_a1 :938`, `_a2 :973`; CltMoments2 `Z, fluc, off, BY, DomHyp, IsoHyp, rhs :84-160`, the private decomposition helpers `:789-967`, `cltMom2_decomp :975`, `_norm_stcltB_le :992`, `_weight_le :1009`, `_moment_fixed :1147`, `_tail_eventually :1198`; MeanFar `meanFar_integrable_L :874`, `_B :881`, `_B_eq :893`, `_B_tr :905`, `_B_sym :920`, `_bad_le :942`, `_B_bound :964`, `_integral_fFar :999`, `_assemble :1031`, `_n_kernel :1356`, `_at_n :1687`, `_eventually :1980` (private `cltMom2G_*`, `meanFarG_*`; the public ones are the 20 names of b9).
- Band only, not restated: CltMoments1 `cltMom1_norm_spin/_norm_xi/_Theta_shift :908-927` (`PropSpin`, shift); the six `CltMom2.…Stmt` defs `:163-224` (no reader); MeanFar `meanFar_K_eq :885`, `_Theta_shift :991`, `_n_K :1495` (supplied by `STKpropsg`, `STThPropsg`), `STMeanFarConcl/STMeanFar/stMeanFar :2088-2134`, all instance sections.
**b3. Hypothesis table (iv)** (band fact read -> premise that supplies it; every fact has one, so the stop rule did not fire)
- `|E n| ≤ 2 - κ`, `κ ≤ Im (mE (E n))` -> `∀ n, κ ≤ (C.m n).im` (`HCltOf` field 6); `‖mE‖ = 1`, `PropSpin` are not read (the weights come from `STThPropsg`).
- `norm_Lloop_le`, `walk_measurable_Lloop`, `etaT`, the law `seqP` -> `CltRepg` (field 11) with `κ ≤ Im m` (`*_lenv_of_rep`), and `IsProbabilityMeasure μ` from `CltRepg.1`.
- `stExpInv_holds` -> `STExpInvgL C μ`; `meanFar_K_eq` with the `Theta` shift/symmetry for `𝒦` -> `STKpropsg` conjunct 1; `meanFar_n_K` (`‖𝒦‖ ≤ c₁/A`) -> conjunct 2.
- `Theta_apply_add_right_of_three_le` -> `STThPropsg` conj 1; `prop5Decay_holds` -> conj 3; `prop6Diff1_holds` -> conj 4; `prop7Diff2_holds` -> conj 5 (conj 2, symmetry, is not read here).
- `STGdecayW` -> `STGdecayWgL` (field 15); `STCltIsoConcl` -> `STCltIsoConclgL` (from `HCltOf` by `stCltIsogL_holds`); `Admissible 𝔠 𝔡` -> field 5; `0 ≤ s < t < 1` -> fields 7-9; the regime `lam²/L² ≤ 1 - t ≤ 1 - s ≤ lam²` -> `STReg5I sz s t`.
**b4. Target statements, extracted by script** (theorems in full, binders `{d} {sz} (C) (μ)` are section variables; the 7 vocabulary definitions cut at 200 characters), and the statement diff against `T2479_*`
```
$ python3 stmts.py <2 files> | grep ": theorem " | grep -v lenv_of_rep
CltMoments2G.lean:56: theorem cltMom1_weight_a1g :: (hd : 3 ≤ d) (hTh : STThPropsg C) : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ n in atTop, ∀ (t : ℝ) (σ : Fin 2 → Bool), σ 0 ≠ σ 1 → 0 < sz.lam n → 0 ≤ t → t < 1 → sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t → ∀ a b : Zd d (sz.L n), sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t a b‖ ≤ C₀ * (1 + 2 ^ (d - 1)) / (((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ^ (d - 2) + 1)
CltMoments2G.lean:83: theorem cltMom1_weight_a2g :: (hd : 3 ≤ d) (hTh : STThPropsg C) : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ n in atTop, ∀ (t : ℝ) (σ : Fin 2 → Bool), σ 0 ≠ σ 1 → 0 < sz.lam n → 0 ≤ t → t < 1 → ∀ a₂ b₁ b₂ : Zd d (sz.L n), ∀ w ρ : ℝ, 2 * d * w ≤ ρ → ρ < ((zdistInf d (sz.L n) (a₂ - b₁) : ℕ) : ℝ) → ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ≤ w → sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t b₂ a₂ - STThg C n (σ 0) (σ 1) t b₁ a₂‖ ≤ C₀ * d * w / (((zdistInf d (sz.L n) (a₂ - b₁) : ℕ) : ℝ) ^ (d - 1) + 1)
CltMoments2G.lean:371: theorem cltMom2_decompg :: (n : ℕ) (s t : ℝ) (hL : cltMom2G_LEnv C n s) (hg : 0 < sz.lam n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : STfFarg C n s t σ a ω - ∫ ω', STfFarg C n s t σ a ω' ∂μ = (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) * CltMom2.flucg C μ n s t σ a ω + CltMom2.offg C μ n s t σ a ω
CltMoments2G.lean:393: theorem cltMom2_norm_stcltBg_le :: (n : ℕ) {s : ℝ} (hL : cltMom2G_LEnv C n s) (σ : Fin 2 → Bool) (β : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ‖STcltBg C n s σ β ω‖ ≤ CltMom2.BYg C n s σ
CltMoments2G.lean:409: theorem cltMom2_weightg_le :: (hd : 3 ≤ d) (hTh : STThPropsg C) : ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, ∀ (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), σ 0 ≠ σ 1 → 0 < sz.lam n → 0 ≤ t → t < 1 → sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t → 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) → ∀ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Zg C n s t σ a β‖ * (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤ CltMom1.uw (a 0) (a 1) (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) M (β 0) * CltMom1.G d (sz.L n) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (β 0 - β 1)
CltMoments2G.lean:499: theorem cltMom2_moment_fixedg :: [IsProbabilityMeasure μ] (hd : 3 ≤ d) {M₀ : ℝ} (hM₀ : 0 < M₀) (n : ℕ) {s : ℝ} (t : ℝ) (hL : cltMom2G_LEnv C n s) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (p : ℕ) (Λ' q₁ εf : ℝ) (h40 : (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ)) (hq₁ : 0 ≤ q₁) (hεf : 0 ≤ εf) (hW : ∀ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Zg C n s t σ a β‖ * (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤ CltMom1.uw (a 0) (a 1) (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) M₀ (β 0) * CltMom1.G d (sz.L n) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (β 0 - β 1)) (hdom : CltMom2.DomHypg C μ n s σ Λ' q₁) (hiso : CltMom2.IsoHypg C μ n s σ p εf) : ∫ ω, ‖CltMom2.flucg C μ n s t σ a ω‖ ^ (2 * p) ∂μ ≤ CltMom2.rhsg C n s t σ a p ((4 : ℝ) ^ d * M₀) Λ' q₁ εf ∧ ∀ θ : ℝ, 0 < θ → μ {ω | θ < ‖CltMom2.flucg C μ n s t σ a ω‖} ≤ ENNReal.ofReal (CltMom2.rhsg C n s t σ a p ((4 : ℝ) ^ d * M₀) Λ' q₁ εf / θ ^ (2 * p))
CltMoments2G.lean:552: theorem cltMom2_tail_eventuallyg :: {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ} {κ : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hrep : CltRepg C μ H₀ g' E) (hTh : STThPropsg C) {s : ℕ → ℝ} (hiso : STCltIsoConclgL C μ s) (t : ℕ → ℝ) : ∃ M : ℝ, 0 < M ∧ ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ (a : Fin 2 → Zd d (sz.L n)) (Λ' q₁ θ : ℝ), κ ≤ (C.m n).im → 0 < sz.lam n → s n < 1 → 0 ≤ t n → t n < 1 → sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n → (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) → 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) → 0 ≤ q₁ → CltMom2.DomHypg C μ n (s n) σ Λ' q₁ → 0 < θ → μ {ω | θ < ‖CltMom2.flucg C μ n (s n) (t n) σ a ω‖} ≤ ENNReal.ofReal (CltMom2.rhsg C n (s n) (t n) σ a p M Λ' q₁ (((sz.W n : ℕ) : ℝ) ^ (-D)) / θ ^ (2 * p))
MeanFarG.lean:631: theorem meanFar_eventuallyg :: {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ} {κ 𝔠 𝔡 Cd : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hAdm : sz.Admissible 𝔠 𝔡) (hm : ∀ n, κ ≤ (C.m n).im) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n < 1) (hrep : CltRepg C μ H₀ g' E) (hreg : STReg5I sz s t) (hG : STGdecayWgL C μ s t Cd) (hTh : STThPropsg C) (hKp : STKpropsg C s) (hX : STExpInvgL C μ) (τ : ℝ) (hτ : 0 < τ) : ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd d (sz.L n), ‖∫ ω, STfFarg C n (s n) (t n) σ a ω ∂μ‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1))
$ python3 stmts.py <2 files> | grep ": def CltMom2" | cut -c1-200
CltMoments2G.lean:142: def CltMom2.Zg :: (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a β : Fin 2 → Zd d (sz.L n)) : ℂ := if Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L 
CltMoments2G.lean:151: def CltMom2.flucg :: (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ := ∑ β : Fin 2 → Zd d (sz.L n), CltMom2.Zg C n s t σ a β * STcltXg C μ n 
CltMoments2G.lean:156: def CltMom2.offg :: (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ := (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.
CltMoments2G.lean:167: def CltMom2.BYg :: (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) : ℝ := (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) * ((etaOf (C.m n) s)⁻¹ ^ 2 + ∑ β : Fin 2 → Zd d (sz.L n), ‖C.K
CltMoments2G.lean:172: def CltMom2.DomHypg :: (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (Λ' q₁ : ℝ) : Prop := ∀ β : Fin 2 → Zd d (sz.L n), ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ)
CltMoments2G.lean:178: def CltMom2.IsoHypg :: (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (p : ℕ) (εf : ℝ) : Prop := ∀ b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n)), (∀ k, ((zdistInf d (sz.L n) ((b k) 0 - (b k) 1)
CltMoments2G.lean:187: def CltMom2.rhsg :: (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (p : ℕ) (M Λ' q₁ εf : ℝ) : ℝ := 2 ^ (2 * p) * (Λ' ^ (2 * p) + (CltMom2.BYg C n s σ * ((Real.
```
`T2479_ThPropsBand`, `T2479_KPropsBand`, `T2479_BandFar` (binding) are targets 7-8, X1b-2. Of the check's statements only the proposal `T2479_MeanFarg` is in this row: the example at `MeanFarG` (it follows from `meanFar_eventuallyg`) against the check text:
```
$ python3 diffcheck.py   (normalises the text of `def T2479_MeanFarg` in the check and of the example in MeanFarG.lean)
check text vs example at MeanFarG.lean:854, whitespace removed, from HCltOf on: identical=True (238 and 238 characters)
```
**b5. Greps** over the statement text of the 20 new public declarations (`stmts.out`), patterns of the ticket target 10
```
$ counts of the five greps (hits in statement text); U-C4 whole-file hits
X1-C1: 0  UBA-C1: 0  TN-C4 (files): 0  X1-C4: 0  U-C4 (def lines): 0
CltMoments2G whole-file hits of Ring.inverse|Matrix.of|Theta d, before / inside the instance section (from line 573): 1 / 3
MeanFarG whole-file hits of Ring.inverse|Matrix.of|Theta d, before / inside the instance section (from line 709): 1 / 10
```
The hits before the instance sections are the `Matrix.of` of `*_lenv_of_rep` (`H₀ n + Matrix.of fun i j => Sizes.seqHflow (sz.withLam g') n u ω i j`, copy of the probe `lenv_of_rep`: the measurability of `H₀ + seqHflow`, which `CltRepg` itself carries; not a kernel). The hits inside the instance sections are the private band producers `*_chk_Th`, `*_chk_K` (band side: `Theta d`, `mSigma`; U-C4 and X1-C1 allow them on band lines) and the band data (`Sizes.seqP szCL`, `STflowE`).
**b6. Registry lines and root imports** (`owedProps`, before `STExp2U`; the scan ran in the whole-library build of b8)
```
$ git diff main...t/T2479 -- RBM3D/Test/Axioms.lean RBM3D.lean | grep "^[+-]"   (cut at 118 characters)
+import RBM3D.Evolution.CltMoments2G
+import RBM3D.Evolution.MeanFarG
+   `RBM.BA.STThPropsg, -- shift, symmetry, `(prop:ThfadC)`, `(prop:BD1)`, `(prop:BD2)` of the mixed-charge carrier pr
+   `RBM.BA.STKpropsg, -- invariance of `𝒦^{(2)}` under translations and the reflection, and `‖𝒦^{(2)}_s‖ ≤ c₁/A`, for
+   `RBM.BA.STCltIsoConclgL, -- the conclusion of `STCltIsogL` (`(eq:bound_isolated)`) over a carrier: hypothesis of `
+   `RBM.BA.CltMom2.DomHypg, -- the per-label tail of the profile-normalised `𝗕` on the window at one `n` (`(eq:propca
+   `RBM.BA.CltMom2.IsoHypg, -- the isolation bound at one `n` (`(eq:bound_isolated)`, `3_5:2245`): a condition on the
```
Before these lines the scan reported exactly `[STThPropsg, STKpropsg, CltMom2.IsoHypg, CltMom2.DomHypg, STCltIsoConclgL]` as unregistered (pre-check: `import RBM3D`, the two modules, `#assert_rbm_axioms`).
**b7. The compiled nonempty instances** (band data of `Step5Inst`, `d = 3`: `szCL`, `bandFM szCL (STflowE zCL)`, `seqP szCL`, `sCL`, `tCL`)
```
$ python3 examples.py <2 files> | cut -c1-200
CltMoments2G.lean:644: example := cltMom1_weight_a1g (bandFM szCL (STflowE zCL)) (by norm_num) cltMo
CltMoments2G.lean:647: example := cltMom1_weight_a2g (bandFM szCL (STflowE zCL)) (by norm_num) cltMo
CltMoments2G.lean:650: example (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a β : Fin 2 → Zd 3 (szCL.L n)) : CltMom2.Zg (bandFM szCL (STflowE zCL)) n s t σ a β = CltMom2.Z szCL n (STflowE zCL n) s t σ a β :=
CltMoments2G.lean:660: example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL) (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) (σ : Fin 2 → 
CltMoments2G.lean:672: example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL) (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) (σ : Fin 2 → 
CltMoments2G.lean:680: example := cltMom2_weightg_le (bandFM szCL (STflowE zCL)) (by norm_num) cltMo
CltMoments2G.lean:684: example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL) (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) (Λ' : ℝ) : ∃ 
CltMoments2G.lean:712: example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL) (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :=
MeanFarG.lean:838: example (hG : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) : ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd 3 (szCL.L n), ‖∫ ω, STfFarg (ban
MeanFarG.lean:854: example {d : ℕ} (κ δ 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ) (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : 
$ sed -n <Target 3e example, 7 lines> CltMoments2G.lean; sed -n <Target 4 example, 14 lines> MeanFarG.lean   (target 3e and target 4, verbatim)
/-- Target 3e: the eventual tail bound, at the band data (`κ = 1/2`). -/
example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
    (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :=
  cltMom2_tail_eventuallyg (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) (κ := 1 / 2) (by norm_num) (by norm_num)
    (cltMom2G_chk_H hLoc hDec).2.2.2.2.2.2.2.2.2.2.1 cltMom2G_chk_Th0
    (stCltIsogL_holds 3 _ _ _ _ _ szCL _ _ _ _ _ sCL tCL (cltMom2G_chk_H hLoc hDec)) tCL

/-- Target 4 at the band data (`κ = 1/2`, `τ = 1/2`); `STThPropsg`, `STKpropsg` are the private band producers above. -/
example (hG : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd 3 (szCL.L n),
      ‖∫ ω, STfFarg (bandFM szCL (STflowE zCL)) n (sCL n) (tCL n) σ a ω ∂(Sizes.seqP szCL)‖ ≤
        ((szCL.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
          (STAI szCL n ^ (-(6 / 5 : ℝ)) / (((zdistInf 3 (szCL.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (3 - 2) + 1)) :=
  meanFar_eventuallyg (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) (g' := szCL.lam) (E := STflowE zCL)
    (H₀ := fun _ => 0) (κ := 1 / 2) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (Cd := 1) (by norm_num) (by norm_num)
    szCL_admissible meanFarG_chk_m sCL tCL (fun _ => le_rfl) szCL_hst meanFarG_chk_t1 (cltRepg_band szCL _)
    szCL_reg5I hG
    (meanFarG_chk_Th szCL (1 / 2) (1 / 10) (STflowE zCL) (by norm_num) (by norm_num) (by norm_num) szCL_WO meanFarG_chk_E)
    (meanFarG_chk_K szCL (1 / 2) (1 / 10) (STflowE zCL) sCL tCL (by norm_num) (by norm_num) szCL_WO meanFarG_chk_E
      (by norm_num) (fun _ => le_rfl) (fun n => (szCL_hst n).le) meanFarG_chk_t1 szCL_reg5I)
    (stExpInvgL_band szCL _) (1 / 2) (by norm_num)
```
**b8. Builds, check file, axioms**
```
$ lake build RBM3D.Evolution.CltMoments2G RBM3D.Evolution.MeanFarG | tail -2; warning counts
info: RBM3D/Evolution/MeanFarG.lean:865:0: 'RBM.BA.meanFar_eventuallyg' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3822 jobs).
warnings in the 2 files: 28, other than the 100-character line limit: 0
$ lake build   (whole library, runs #assert_rbm_axioms; lines of its log)
5853:registry: 2 borrowed + 111 owed + 122 structural + 7 refuted + 18 superseded; 125 registered premise
5979:Build completed successfully (4320 jobs).
 RBM.BA.STThPropsg: 5 [no certificate]; RBM.BA.STKpropsg: 1 [no certificate]; RBM.BA.STCltIsoConclgL: 2 [no certificate]; RBM.BA.CltMom2.DomHypg: 2 [no certificate]; RBM.BA.CltMom2.IsoHypg: 1 [no certificate];
$ lake env lean docs/tickets/checks/T2479-check.lean
exit=0 error-lines=0
$ #print axioms of all 20 public declarations (scratch ax_all.lean, names from stmts.py)
standard three: 20; other: 0; names printed: 20; sorry|admit|native_decide|axiom hits: 0
```
**b9. Name clash** of the 20 new public names and the stems `cltMom2G_`, `meanFarG_`
```
$ for r in main <9 t/T24xx branches>: git grep -nE "<20 names, 2 stems>" $r -- RBM3D/*.lean RBM3D.lean | wc -l
main: 0  t/T2469b: 0  t/T2471b: 0  t/T2472: 0  t/T2474: 0  t/T2473: 0  t/T2475: 0  t/T2476: 0  t/T2477: 0  t/T2478: 0  
hits on t/T2479 outside the 2 new files: RBM3D/Test/Axioms.lean:222 RBM3D/Test/Axioms.lean:223 RBM3D/Test/Axioms.lean:224 RBM3D/Test/Axioms.lean:225 RBM3D/Test/Axioms.lean:226 
```
The 5 hits on `t/T2479` are the comment lines of the registry entries (b6).
**b10. X1-C5 tripwire** (`g` = (added+removed)/band lines of the aligned block, `f_sem` = band lines moved to the band producers of target 7/8, hand-counted ranges `MeanFar:1053-1056,1062-1064`, `1784-1797`, `2044-2073`, `CltMoments1:908-927`, and the 24 K/Θ lines of `MeanFar:874-1026` as X1a counted them)
```
$ python3 gtab.py
block               band  gen  added removed  g=(a+r)/band   moved-to-band-producer lines  f_sem
MeanFar 874-1026     153  139    86     100         1.216                             24  0.157
MeanFar 1028-1108     81   70    23      34         0.704                              7  0.086
MeanFar 1353-1491    139  139    19      19         0.273                              0  0.000
MeanFar 1684-1914    231  209    38      60         0.424                             14  0.061
MeanFar 1977-2082    106   81    26      51         0.726                             30  0.283
CltMom2 783-984      202  162    68     108         0.871                              0  0.000
CltMom2 986-1208     223  187    93     129         0.996                              0  0.000
CltMom1 904-1031     128   84    55      99         1.203                             19  0.148
```
**Narrative.**
1. Row. X1b-1 of the pre-signed split: targets 1-3 in `CltMoments2G` (`cltMom1_weight_a1g/_a2g`, vocabulary `CltMom2.Zg … rhsg`, `cltMom2_decompg`, `_norm_stcltBg_le`, `_weightg_le`, `_moment_fixedg`, `_tail_eventuallyg`), target 4 in `MeanFarG` (`meanFar_eventuallyg`). No band, chain, induction or BA file is edited (b1); each new file has exactly its two Layout imports.
2. Size. 729 / 869 lines against the stop line 2,000 (b1); (a) predicted 546 / 637 with the instance sections excluded, the ticket's drafting central was 600 / 500. The instance sections are 157 and 161 lines (`CltMoments2G:573-729`, `MeanFarG:709-869`; they hold the private producers of note 7), without them 572 and 708. No stop rule fired: no file above 2,000, no premise beyond (a)-(d) (b3), no `BA/*` or `IniTerm*` import, no second propagator, no comparison text (b5), `f_sem` at most 0.283 (b10).
3. Method. Restatement of merged band text over `(C, μ)` with the carrier propagator `STThg`: the weights read `STThPropsg` conjuncts 1, 3, 4 through `meanFar_T1`; the mean part reads `STThPropsg` 1, 3, 5, `STKpropsg`, `STExpInvgL`, `STGdecayWgL`; the loops come from `CltRepg` and `κ ≤ Im m`. Sources: the band files at the base `35b7d6cb` and the probe text `t/T2455` (`8eb4ff2a`) `RBM3D/Probe/T2455Meas.lean:55-369`, read with `git show`, never merged. Nothing from RBM1D or RBM2D was used, so no sister-project diff-stat applies.
4. Target 4 states its premises as the fields of `HCltOf` it reads (`hAdm`, `hm`, `hs0`, `hst`, `ht1`, `hrep`, `hG`) plus `STReg5I`, `STThPropsg`, `STKpropsg`, `STExpInvgL`, not `HCltOf` itself: with the Layout imports (`MeanFar`, `CltGen`) `cltGood_hCltOf_szCL` is not in scope (`#check` after those two imports: unknown identifier), so the instance could not build `HCltOf`. The proposal `T2479_MeanFarg` follows (b4, identical text). `κ' = κ` (the band took `min κ (1/2)` because it only had `|E| ≤ 2 - κ`).
5. Registry. 5 lines, 3 more than the 2 expected: `STCltIsoConclgL`, `CltMom2.DomHypg`, `CltMom2.IsoHypg` are binders of public theorems and no theorem concludes them (b6). The two root import lines are in `RBM3D.lean` (the ticket lists it as writable), so the whole-library build and the scan ran (b8).
6. The pairs `cltMom2G_LEnv`/`meanFarG_LEnv` and `*_lenv_of_rep` are the same text twice: the two files do not import each other (Layout); `CltFarG` imports both and can identify them by `Iff.rfl`.
7. Instances (b7). Discharged at `szCL`, `d = 3`, `sCL`, `tCL`: `HCltOf` (`cltGood_hCltOf_szCL`), `STCltIsoConclgL` (`stCltIsogL_holds`), `STReg5I`, `STExpInvgL`, `CltRepg`, the admissibility, `κ = 1/2 ≤ Im m`, `0 ≤ sCL < tCL < 1`, the loop envelope, `n ≥ 34` (`40 ≤ log W`), `q₁ = 1`, `εf = W^{-1}`. The only hypotheses of the examples are the Step 2 pins `STLocalEntryUgL`, `STGdecayWgL` (as X1a). `STThPropsg` and `STKpropsg` at the band data are proved by the private `cltMom2G_chk_Th` (`CltMoments2G`) and `meanFarG_chk_Th`, `meanFarG_chk_K` (`MeanFarG`): the statements of the second row's targets 7a, 7b (`prop5Decay_holds`, `prop6Diff1_holds`, `prop7Diff2_holds`, `bandFM_STThg`, `KLK_two`, `meanFar_T1`, `meanFar_n_K`), written here only so that no deterministic premise is left open; the files may not import each other, hence one copy of 7a per file.
8. Estimate for X1b-2 (an extrapolation, not a measurement): like for like (instance sections excluded) actual over (a)'s central for X1b-1 is (572 + 708)/(546 + 637) = 1280/1183 = 1.08, so `CltFarG` about 958 × 1.08 ≈ 1,040 lines plus its instance section, far below the 1,800 reserve line; `CltFarG2` is not needed.
## (c) Verified Mathlib names (each by `#check` in a scratch file importing `RBM3D.Evolution.MeanFarG`: exit 0, 0 errors; names verified absent: none searched)
`Filter.Eventually.exists`; `Filter.eventually_ge_atTop`; `MeasureTheory.prob_le_one`; `div_le_self`; `Finset.single_le_sum`; `MeasureTheory.Integrable.of_bound`; `MeasureTheory.integral_finsetSum`; `MeasureTheory.integrable_finsetSum`; `MeasureTheory.integral_sub`; `Measurable.of_eval_matrix`; `Real.log_two_gt_d9`; `Real.log_two_lt_d9`; `Real.rpow_le_rpow_of_nonpos`; `ENNReal.toReal_mono`; `MeasureTheory.Measure.real`; `pow_add_pow_le`; `Nat.lt_floor_add_one`; `Finset.sum_filter`; `Fintype.sum_prod_type`. All other Mathlib names occur in text copied from merged band files (compile-checked).

## (d) Open issues and paper-delta candidates
- O1 (question for the dispatcher). Target 7 is written three times in private form (`cltMom2G_chk_Th`, `meanFarG_chk_Th`, `meanFarG_chk_K`, note 7); X1b-2's public `bandFM_STThPropsg`, `bandFM_STKpropsg` (statements of `T2479_ThPropsBand`, `T2479_KPropsBand`) duplicate them. Either accept the duplicates (X1b-2 proves target 7 publicly in `CltFarG` as planned), or have this row's repair make 7a/7b public in `MeanFarG` and drop target 7 from X1b-2; I did not pick, because the split places target 7 in `CltFarG`.
- O2. The `T2479_MeanFarg` shape with `HCltOf` is an example, not the theorem (note 4). O3. Registry lines beyond the two expected (note 5). O4. `RBM3D.lean` import lines added here (note 5); the hub's step 4 is then a no-op. O5. Duplicated `LEnv` pair (note 6).
- O6. Build: 28 warnings in the two files, all the 100-character limit on docstring lines, as in `CltGen`, `CltMoments1` (b8).
- O7. X1-C5: `f_sem` is 0.283 on `MeanFar:1977-2082` (30 of 106 lines: `hEn`, `hκ'`, `h5n`, `h7n`, exactly the band producers of target 7a), below 0.30 but close; 0.157 on `MeanFar:874-1026`, at most 0.148 elsewhere (b10). Reported as the stop rule asks; no twin is needed since the generic text compiles.
- Paper-delta candidates. `T2479a`: the constants of the weights and of the mean part come from the pin `STThPropsg` (`M = 4^d C₅ (1 + 2^{d-1}) C₆ d`), not from `(d, Λ, κ)` as in the band `CltMom2.WeightStmt` and `meanFar_eventually`. `T2479b`: the mean part needs `κ ≤ Im (C.m n)` only (`κ' = κ`), not `|E| ≤ 2 - κ` (X1-C1, same family as X1a's candidates). No other Lean/paper statement difference was found in targets 1-4 (mixed charges `σ 0 ≠ σ 1` are the index set of `STCltFarConcl` and the range of the pins `STThPropsg`, `STKpropsg`, as the ticket fixes).
