Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 03:24:21 UTC 2026
Notation: `N = sz.size n`, `B_u = Bctl n u`, `X m n := XL m n (v n)`, `Y m n := XLK m n (v n)`, `ζ(u) = B_u^{1/6} XLK n_ n u + STbootRHS 2 (XL · n u)(XLK · n u) B_s n_ p`. Scripts (Python, no Lean; mpmath 40 digits / `Fraction`) in `$SCR` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2246` (`defs.py` transcribes `STbootRHS`, `STn12(E)`, `nqLinPhi1-3`, `Bparam`, `nqFlowLam/PhiC` from the merged files and the check file §2). `main` = b35643d (the worktree is at it).
### (i) Exponent table
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | `𝔠d := min(min 𝔠d_G 𝔠d_L)(1/(2d))` (`𝔠d_G`, `𝔠d_L` of `gridGoodN_holds d`, `nqLinGood_holds d` at the same `(κ,ε,𝔡,C_d)`, which do not depend on `s,t`) | `0<𝔠d ≤ 𝔠d_G ≤ 1/100`; `d𝔠d ≤ 1/2 < 1` (`st_window`) | `1/2` (`1 − d𝔠d`) |
| 2 | `STConStInd 𝔠d s t ⇒ STConStInd 𝔠d_* s t` (`𝔠d_* ∈ {𝔠d_G,𝔠d_L}`) | `B_t^{𝔠d} ≤ ratio < 1`, `B_t > 0` ⇒ `B_t < 1` ⇒ `B^{𝔠d_*} ≤ B^{𝔠d}` as `𝔠d ≤ 𝔠d_*` (the weaker exponent is the larger one) | exact |
| 3 | window `[s,v]` (`s<v≤t`) for `gridGoodN_holds` | `st_conStInd_sub` needs `s≤s, s<v, v≤t, t<1`; `STStep2Concl s v`: `precomp_param` along `TimeIcc s v ⊂ TimeIcc s t` (`STGdecayW` right side has `s,u` only) | none lost |
| 4 | section → `v` (`v n = u_n` if `s n < u_n`, else `t n`) → `Λ_s = max 1 (nqFlowLam X B_s n_ p)`, `Φ₁,Φ₂,Φ₃`, `Φc = nqFlowPhiC X Y n_` (all fixed before `τ, D`) | `nqGridEndLinN` binds `Λ,Φ_i,v` before `∃ ε₁ τ' D' C_K` and `Φc, K` after it: order fits | — |
| 5 | `ε₀ = τ/2`, `D₁ = D+2`; `e0 = min ε₀ 1`, `ε₁ = e0/8`, `ε = min(e0/(8C),1/2)`, `τ' = ε/2`, `D'' = C+k+2+(4k+2)/𝔠`, `D' = D''+1`, `C_K = D₁+2C_P*+6k+20+D''` (`NQEndLin.lean:1050-1056`; `C = nqGood1C>0` abstract) | `ε₁,τ',D'>0`, `C_K ≥ 0`; rows below | `C_K ≥ 133` in the rows below |
| 6 | grid `K n = max 1 ⌈N^{C_K}⌉₊`; `gridGoodN_holds`, `nqLinGood_holds` at `C := C_K+2`, `ε := ε₁` | `N^{C_K} ≤ K ≤ ⌈N^{C_K}⌉`, `K ≠ 0`, `K+1 ≤ N^{C_K}+2 ≤ N^{C_K+2}` for `N ≥ 2` | `N^{C_K}(N²−1) ≥ 2` |
| 7 | failure probability | `P(Gᶜ) ≤ N^{-(D+2)}`, two good events `≤ N^{-(D+2)}` each (`HighProbAt`, `D+2`), initial event (`STLK s` at `(ε₁, D+2)`): `4N^{-(D+2)} ≤ N^{-D}` | `N²/4 ≥ 1` for `N ≥ 2` |
| 8 | final loss | `N^{τ/2}(Λ_s^{1/2}+Φ₁+Φ₂+Φ₃) ≤ N^{τ/2} ζ ≤ N^τ ζ` (`N ≥ 1`); ratio `(Λ_s^{1/2}+ΣΦ)/ζ ≤ 1`, no `3` and no eventual needed | `N^{τ/2}`; max ratio `1.000000000000`, 0 violations |
| 9 | `Λ_s ≥ 1`, `Φ_i ≥ 0`, `Φc ≥ 1`, `Φc ≥ X_m (m≤n_+1)`, `Φc ≥ Y_m (m≤n_)` | `max 1`; sums of `≥ 1` terms; pair hypotheses cover `STlenL n_ p m` for `m ≤ n_+1`, `2n_−1`, `4p` and `XLK` for `m ≤ n_` | 0 violations (row below) |
| 10 | G1 (the level) | `Λ_s^{1/2}` = first summand of `STbootRHS 2 … B_s` exactly (when `≥ 1`; else `1 ≤ 1 + Φ₃ ≤ S2 ≤ ζ`) | row `0` |
| 11 | collapsed indices `u_n = s_n` | `‖𝓛−𝒦‖_s/B_s^{n_} ≺ 1 ≤ 3 ≤ S2 ≤ ζ` by `STLK s` at length `n_ ≥ 1` | `ζ ≥ 3` |
| 12 | `STbootRHS lo XL XLK B n_ p` antitone in `B>0` (bridges `STNQConcl'→''`, `STXiBoot→'`) | `s n ≤ u ≤ t n < 1` ⇒ `B_s ≤ B_u` (`STBctl_mono`), `B_s>0` (`st_Bctl_pos`); only the first summand has `B`, exponent `−1/(4p) < 0` | row below (0 violations) |
Constants (`python3 consts.py`; `C_P* = 11+(4k+4)(1−τ_R)`, `τ_R = 1/2`, the witness of T2199 (a); only `C_P* ≥ 0` is used):
```
tau  D  k  C | e0=min(tau/2,1) eps1 eps tau' D'' D' C_P* C_K ; D1=D+2 | K+1<=N^(C_K+2) needs N>=2 ; 4N^-(D+2)<=N^-D needs N>=2
0.1   1 2 0.5 | 0.05 0.00625 0.0125 0.00625 64.5 65.5 17 133.5
0.1   1 3 1.0 | 0.05 0.00625 0.00625 0.003125 90 91 19 169
0.1   1 6 20.0| 0.05 0.00625 0.0003125 0.00015625 184 185 25 293
0.01  3 2 0.5 | 0.005 0.000625 0.00125 0.000625 64.5 65.5 17 135.5
0.01  3 3 1.0 | 0.005 0.000625 0.000625 0.0003125 90 91 19 171
0.01  3 6 20.0| 0.005 0.000625 3.125e-05 1.5625e-05 184 185 25 295
```
Absorption rows of the merged `nqGridEndLinN` (its 24-hypothesis budget, formulas of T2199 `exps.py`, re-run at `ε₀ = τ/2`; `python3 table.py | grep -E ...`; worst over `k∈{2,3,6}, C∈{1/2,1,5,20}, Im m∈{1/2,0.968,1/10}, W∈{N^{1/6},N^{1/3}}`; the other rows `he1,he3,hdelta,heta,hDeta,K+1,W≥2` are `≤ 0` for `log10 N ≥ 4` or negative throughout; full output in `table.out`):
```
=== tau=0.1 D=1: eps0=tau/2=0.05, D1=D+2=3
row | worst log10(LHS/RHS) at log10N = 1,2,3,6,48.6,51.5,56.2,100,1000 | crossover x*(last positive scan point, log10N)
ha1                  +0.7 +0.7 +0.7 +0.5 -1.2 -1.4 -1.6 -3.4 -40.9 | 17.78
ha2                  +3.2 +3.4 +3.6 +3.8 +3.2 +3.1 +3.0 +1.7 -29.2 | 141.3
ha3                  +2.1 +2.2 +2.3 +2.3 +1.3 +1.2 +1.0 -0.4 -31.8 | 79.43
he2                  +8.7 +6.0 +3.2 -5.0 -114.3 -121.3 -132.6 -238.5 -2414.5 | 3.981
union D1=D+2->D      -1.4 -3.4 -5.4 -11.4 -96.6 -102.4 -111.8 -199.4 -1999.4 | 0.2818
W^eps>=4             +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 +0.5 | 1.122e+04
d*W^(eps/2)<=W^eps   +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 | 1.778e+04
exact slacks e0-exponent (min over k,C): {'ha1: Ce+e1': '3/80', 'ha2: Ce+2e1': '1/32', 'ha3: eq+Ce+e1': '1/32'} 
=== tau=0.01 D=3: eps0=tau/2=0.005, D1=D+2=5
row | worst log10(LHS/RHS) at log10N = 1,2,3,6,48.6,51.5,56.2,100,1000 | crossover x*(last positive scan point, log10N)
ha1                  +0.8 +0.8 +0.8 +0.8 +0.6 +0.6 +0.5 +0.4 -3.4 | 177.8
ha2                  +3.2 +3.5 +3.7 +4.0 +4.7 +4.7 +4.8 +4.9 +2.7 | 1778
ha3                  +2.2 +2.3 +2.4 +2.5 +2.8 +2.8 +2.8 +2.8 +0.1 | 1000
he2                  +8.8 +6.1 +3.4 -4.8 -112.4 -119.3 -130.5 -234.7 -2376.0 | 3.981
union D1=D+2->D      -1.4 -3.4 -5.4 -11.4 -96.6 -102.4 -111.8 -199.4 -1999.4 | 0.2818
W^eps>=4             +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 | 1.122e+05
d*W^(eps/2)<=W^eps   +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 | 1.778e+05
exact slacks e0-exponent (min over k,C): {'ha1: Ce+e1': '3/800', 'ha2: Ce+2e1': '1/320', 'ha3: eq+Ce+e1': '1/320'} 
```
Every row is `≤ 0` eventually; `ha2` crosses at `log10 N ≈ 141` (`τ=1/10`) and `1778` (`τ=1/100`), the two `W^ε` rows at `1.1·10^4`–`1.8·10^5` (inherent in `ε = e0/(8C)`, T2199 (i.3)); all are `∀ᶠ n` thresholds, never hypotheses. Exact slacks of `ha1, ha2, ha3` are `3/4, 5/8, 5/8` of `ε₀`.
**G1 (level `Λ_s`).** `python3 g1.py` (`d=3`, `W=N^{0.3}`, `L^d=N^{0.1}`, `lam=W^{-d/2+1/10}`, `1−t=N^{-1/2}`, `v=t`, `𝔠d=1/100`, `1−s=(1−t)/B_t^{𝔠d}`, i.e. equality in `(con_st_ind)`; XL=1 and `XL(m)=N^{m/10}`), rows `log_N(Λ_s^{1/2}/first summand)` at `B_s` (R2*) and at `B_t` (T2207 draft):
```
log10N= 3 caseI True window True con(=,to 1e-30) True s>=0 True  g^2/(1-s)=9.32e-02  log_N(B_t/B_s... ) B_s<=B_t True
log10N=30 caseI True window True con(=,to 1e-30) True s>=0 True  g^2/(1-s)=4.79e-11  log_N(B_t/B_s... ) B_s<=B_t True
p=1 k=3 log10N= 1 XL=1         first(B_s)=1.143e+00>=1:True  R2* row=0.00e+00 | T2207 row=0.00049 (pred 0.00057)
p=1 k=3 log10N= 3 XL=1         first(B_s)=1.840e+00>=1:True  R2* row=0.00e+00 | T2207 row=0.00083 (pred 0.00087)
p=1 k=3 log10N= 6 XL=1         first(B_s)=3.821e+00>=1:True  R2* row=0.00e+00 | T2207 row=0.00095 (pred 0.00096)
p=1 k=3 log10N= 6 XL=N^(m/10)  first(B_s)=4.810e+02>=1:True  R2* row=0.00e+00 | T2207 row=0.00095 (pred 0.00096)
p=1 k=3 log10N=30 XL=1         first(B_s)=1.071e+03>=1:True  R2* row=0.00e+00 | T2207 row=0.00100 (pred 0.00100)
p=4 k=6 log10N= 1 XL=1         first(B_s)=1.034e+00>=1:True  R2* row=0.00e+00 | T2207 row=0.00012 (pred 0.00014)
p=4 k=6 log10N= 6 XL=N^(m/10)  first(B_s)=1.111e+04>=1:True  R2* row=0.00e+00 | T2207 row=0.00024 (pred 0.00024)
p=4 k=6 log10N=30 XL=1         first(B_s)=5.721e+00>=1:True  R2* row=0.00e+00 | T2207 row=0.00025 (pred 0.00025)
```
R2* row `0` (to `1e-40`) at every printed point; the summand is `≥ 1` at all of them (`g1.out`: 28 points). The T2207 row is `𝔠d·log_N(1/B_t)/(4p)` (`≈ 0.4·𝔠d/(4p)`, the `pred` column), `≤ 𝔠d/(4p)`; it is what R2* removes. **Data note:** the ticket's literal `1−s = N^{𝔠d}(1−t)` is not admissible under `(con_st_ind)` (`B_t^{𝔠d} > N^{-𝔠d}`: `0.976>0.933`, `0.948>0.871`, `0.759>0.501` at `log10 N = 3, 6, 30` for `W=N^{0.3}`), so the extremal admissible ratio `B_t^{𝔠d}` is used; no effect on the verdict. **G1: PASS.**
**Degree-1 / bridge / `Φc` checks (ii, iii, v)** `python3 deg1.py` (40000 random `k∈[2,9], p∈[1,6], XL,XLK∈[1,10^8], B_s≤B_v≤1`):
```
cases 40000  max (Lam^1/2+Phi1+Phi2+Phi3)/zeta = 1.000000000000  violations(>1): 0
bridge: STbootRHS(B_v) <= STbootRHS(B_s) for B_s<=B_v: violations 0
Phi_c >= X_m (m<=k+1), >= Y_m (m<=k), >= 1: violations 0
STn12E k in [k-1,k+1]: True
STn12 m, m in Icc((k+1)/2+1)(k-1): lengths in [1,k-1]: True
S2=sum_{m=k-1}^{k+1} XL_m >= 3 and 1 + Phi3 <= S2: violations 0
```
`Φc` enters `nqGridEndLinN` only as its `∀` binder and the `GoodSetN` argument (`awk 'NR>=1067&&NR<=1115' RBM3D/Induction/NQEndLin.lean | grep -c Φc` = 2) and `GridGoodNConcl` asks only `∀ n, 1 ≤ Φ n` (`GridGoodN.lean:507`): the sum choice `Φc = Σ_{m∈Icc 1 (n_+1)}(X m + Y m)` needs no `N^{C₀}` (T2207 fallback not needed). **G4 / premises: PASS** (rows 1-3; `RangeCond (ε/2) t`, `|E n| < 2−κ/2`, `t n < 1` from `v3_premises_of_stFlow` `Green/Pins.lean:1049` with `nqGridEndLinN` at `κ/2`, `τ = ε/2`; `W⁻¹ ≤ (1−t)/(1−s)` from `st_window` at `𝔠d`, `d𝔠d<1`; `Admissible` gives `SizeTendsto, Bandwidth, WO`; `STCaseI` is the regime).
**Transfers (iv).** Initial: `STLK s` at `k = n_` is `Prec` over the finite `(σ,a)`, its bad set is `{∃(σ,a), N^{ε₁}B_s^{n_} < ‖·‖}`; `pathP.map (pathH s v K n 0) = seqP.map (seqHflow n (gridTime … 0))` (`map_pathH_eq`, `Path/Walk.lean:598`, needs `0 ≤ s`, `s ≤ v`, `K n ≠ 0`) and `gridTime … 0 = s n`; terminal: `gridTime … (K n) = v n` (`gridTime_last`). `STLKM … (seqHflow n u ω) = Lloop − STKloop` by `rfl`; the matrix event is measurable: `walk_measurable_loopFine` (`Path/Walk.lean:794`) minus the constant `STKloop`, as `gridGood_meas_loopFine` (`GridGoodN.lean:266`); `Measure.map_apply` needs that. **Bridges (v): PASS** (no stochastic input: `Prec` is monotone in the right side, `StochDomAt.of_subset`, `N^τ ≥ 0`; `STOeqNQ'→''`, `STOeqQt→'`, `STOeqQtNZ→'` unfold `STIngR` and get `t n < 1` from `lemT_lt_one` as `stOeqNQ'_of_stOeqNQ` `Step34PinsP.lean:156`).
### (ii) One concrete nondegenerate instance
Data (`d=3`, `sz0`, `z0 n = 1/2 + i N^{-4/5}`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `s=0`, `t=1/16`, `C_d=1`; `n_=3`, `p=1`, `XL≡XLK≡1`, `τ=1/10`, `D=1`; non-collapsed section `u=v=1/32` and collapsed `u=s`). `python3 inst.py`:
```
n=0: L=4 W=32 lam=0.015625 N=2^21
z0(0)=1/2+i*8.764e-06  msc(z0)=(-0.249998868589 + 0.968241454626j)  lemE=0.500000 lemT=0.999990949
3<=d, kappa,eps,fd,C_d>0                                                                             True
0<=s<t<=lemT(z0 0): 0<1/16<=0.999991                                                                 True
|E|<=2-kappa/2=1.95 (nqGridEndLinN gets kappa/2; |lemE|<=|Re z|=1/2)                                 True
RangeCond(eps/2): N^(-1+eps/2)=9.873e-07 <= 1-t=15/16                                                True
STCaseI: lam^2/L^2=1.526e-05 <= 1-t                                                                  True
window W^-1=1/32 <= (1-t)/(1-s)=15/16                                                                True
Bandwidth 1/6: N^(1/6)=11.314 <= W=32                                                                True
WO 1/10: W^(-3/2+1/10)=0.00781 <= lam=0.01562 <= 10                                                  True
s<u<=t for the non-collapsed section: 0<1/32<=1/16                                                   True
0<B_s=3.0987e-05 <= B_u=3.1986e-05 <= B_t=3.3052e-05 < 1 (STBctl_mono, st_Bctl_pos)                  True
section u=1/32: Lam_s=max(1,nqFlowLam)=179.643070 ; Lam^1/2=13.403099 ; first summand of STbootRHS 2 at B_s=13.403099
Phi1=1.0 Phi2=0.178167 Phi3=1.0 Phi_c=8.0 ; S1=1.0 S2=3.0 S3=0.0 ; zeta=17.581266
Lam^1/2+Phi1+Phi2+Phi3 = 15.581266 <= zeta = 17.581266 : True ;  N^(tau/2)*that = 32.2615 <= N^tau*zeta = 75.3725
collapsed u=s: zeta(s) >= S2 = 3.0 >= 3 >= 1 (bound by STLK s: |L-K|/B_s^3 << 1)
k=3 index sets: Icc 2 2={2}, Icc((3+1)/2+1=3)(2)=empty ; STn12E 3=(3, 3) ; Icc(2)(4) for XL: S2 sum m=2..4
c'=0.01: B_t(n)^c' <= 15/16 for all 2(n+1) >= exp(0.4366), i.e. log10(n0) ~ 0.1896 (eventual only; the instance never evaluates n)
c'=1.0e-6: B_t(n)^c' <= 15/16 for all 2(n+1) >= exp(4303), i.e. log10(n0) ~ 1869 (eventual only; the instance never evaluates n)
n=10: log_N B_s^(-1/4) = 0.200828 (limit 15/72 = 0.208333); zeta(u=s)>=3 trivially; Lam_s>=1: True
n=1000000: log_N B_s^(-1/4) = 0.206688 (limit 15/72 = 0.208333); zeta(u=s)>=3 trivially; Lam_s>=1: True
n=1000000000000: log_N B_s^(-1/4) = 0.207487 (limit 15/72 = 0.208333); zeta(u=s)>=3 trivially; Lam_s>=1: True
```
Every hypothesis holds at `n=0` (no `N=0`, no empty index, window `[0,1/16]` nondegenerate, `v=1/32>s`); `Icc((n_+1)/2+1)(n_−1) = ∅` at `n_=3` (so `S3 = 0`, `Φ₂ = B_v^{1/6}`), `Icc 2 (n_−1) = {2}`. The `∀ᶠ n` conclusion is never evaluated; `STConStInd 𝔠d` (`∀ᶠ`, `𝔠d` abstract from the merged theorems) is discharged for every `𝔠d>0` by `sz0_con` — threshold `log10 n0 ≈ 0.19 / 1.9 / 1869` for `𝔠d = 10^{-2}/10^{-3}/10^{-6}`, never evaluated. **Limit computation for the new quantity**: `log_N B_s^{-1/4} → 15/72` along `sz0` (rows `n=10 … 10^12`), `Λ_s ≥ 1`, `ζ ≥ 3` throughout. **External hypotheses**: no new one. `STKbound, STKward, STLK, STStep2Concl` (other gates' pins, as `InstIngConcl`) and the pair hypotheses (`Prec` of `Ξ̂ ≺ XL, XLK ≡ 1`, the Step 3 conclusion `STLmaxU`) stay hypotheses of the examples; nothing in this ticket needs them beyond their statements (`B_s^{n_} > 0`, `ζ ≥ 3`, printed above).
### Verdicts
- Target 1 (ten pin texts, vocabulary): PASS (definitions; the one-token diffs are checked by the check file compile, §4 of the ticket).
- Target 2 (bridges): PASS (row 12; `STNQConcl'→''`, `STXiBoot→'` need `∀ n, t n < 1` as pinned).
- Target 3-5 (window facts, levels, per-section endpoint): PASS (rows 1-11, G1, G4, Φc, transfers).
- Target 6 (`stOeqNQPT''_holds`): PASS (`perTimeDomAt_iff_forall_section` needs `U n` nonempty: `s n ≤ t n`, the constant sign vector is non-alternating for `n_ ≥ 2`, `Zd d L` nonempty).
- Findings (no verdict change): (1) literal G1 data not `(con_st_ind)`-admissible (above); (2) `3N^{τ/2} ≤ N^τ` is not needed (row 8); (3) `STConStInd 𝔠d ⇒ STConStInd 𝔠d_*` goes from the smaller to the larger exponent (row 2; the ticket calls this "antitone"); (4) HEAD of `main` is b35643d, with T2245 merged (`git log -1`), so registry Case A applies.

## (a′) Preflight corrections — Tue Oct  6 04:15:05 UTC 2026
Finding (4) of (a) cites `git log -1` for "T2245 merged"; `git log -1` at `b35643d` is the T2244 merge. The fact stands (below); no verdict changes; registry Case A applied.
```
$ git log --oneline -2 b35643d; git show b35643d:RBM3D/Test/Axioms.lean | grep -n "^def supersededProps"
b35643d T2244: merge UN-09 Universality/GUELocalBootstrap
05e5052 T2245: merge ST main-induction regime assembly Induction/MainIndRegimes
379:def supersededProps : List Name :=
```
## (b) Script output
Branch `t/T2246`: commits `4e9b91f` (pins, proofs, instances, registry) and `8c1a9b5` (docstring fix only); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2246`, base `b35643d`. Suite run on `8c1a9b5`: START Tue Oct  6 04:13:19 UTC 2026; END Tue Oct  6 04:14:15 UTC 2026 (`date -u`). Scripts and outputs in `$SCR` (as in (a)).
```
$ lake build RBM3D.Induction.NQEndFlow 2>&1 | grep -E "NQEndFlow|Build completed"    # 20 lines; the five public targets and the instance:
info: RBM3D/Induction/NQEndFlow.lean:1090:0: 'RBM.Gauss.Sizes.stXiBoot'_of_stXiBoot' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/NQEndFlow.lean:1091:0: 'RBM.Gauss.Sizes.stOeqNQ''_of_stOeqNQ'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/NQEndFlow.lean:1092:0: 'RBM.Gauss.Sizes.stOeqQt'_of_stOeqQt' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/NQEndFlow.lean:1093:0: 'RBM.Gauss.Sizes.stOeqQtNZ'_of_stOeqQtNZ' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/NQEndFlow.lean:1094:0: 'RBM.Ind.stOeqNQPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/NQEndFlow.lean:1095:0: 'RBM.Ind.NQEndFlowInst.inst_OeqNQPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3845 jobs).
# 18 of the 18 `#print axioms` lines (file lines 1078-1095: 12 definitions, 5 targets, 1 instance) are exactly [propext, Classical.choice, Quot.sound]; lines with warning/error: 0
$ lake build 2>&1 | tail -1      # whole library; the root does not import the new module yet (hub, at merge)
Build completed successfully (4049 jobs).
$ python3 extract_targets.py      # the six pinned statements, signatures read from the file (examples pinning them: file lines 282, 1065-1070)
RBM3D/Induction/NQEndFlow.lean:921: theorem stOeqNQPT''_holds : ∀ d : ℕ, STOeqNQPT'' d
RBM3D/Induction/NQEndFlow.lean:266: theorem stOeqNQ''_of_stOeqNQ' : ∀ d : ℕ, STOeqNQ' d → STOeqNQ'' d
RBM3D/Induction/NQEndFlow.lean:235: theorem stXiBoot'_of_stXiBoot {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (ht1 : ∀ n, t n < 1) (h : STXiBoot sz E s t) : STXiBoot' sz E s t
RBM3D/Induction/NQEndFlow.lean:271: theorem stOeqQt'_of_stOeqQt : ∀ d : ℕ, STOeqQt d → STOeqQt' d
RBM3D/Induction/NQEndFlow.lean:276: theorem stOeqQtNZ'_of_stOeqQtNZ : ∀ d : ℕ, STOeqQtNZ d → STOeqQtNZ' d
RBM3D/Induction/NQEndFlow.lean:217: private theorem stNQConcl''_of_stNQConcl' (sz : Sizes d) (E s t : ℕ → ℝ) (ht1 : ∀ n, t n < 1) (h : STNQConcl' sz E s t) : STNQConcl'' sz E s t
$ python3 stmt_diff2.py           # the 12 definitions vs docs/tickets/checks/T2246-check.lean section 2 (binders `{d : ℕ} (sz : Sizes d)` normalised)
IDENTICAL (name(lines)): STNQConcl''(13), STXiBoot'(9), STNQConclPT''(13), STOeqNQ''(1), STOeqQt'(1), STOeqQtNZ'(1), STIterR'(13), STIterations'(1), STIterationsII'(1), STOeqNQPT''(1), nqFlowLam(2), nqFlowPhiC(2)
blocks differing: 0
$ lake env lean stmt_check.lean   # check-file sections 2-4 (namespace T2246Check) + `example : T2246_stOeqNQPT''_holds := @RBM.Ind.stOeqNQPT''_holds`, the four bridges, `rfl` for the 12 definitions
exit 0, 0 bytes of output (22 examples)
$ python3 merged_tokdiff.py       # new pin text vs the merged text, token level (the hunks allowed by the ticket)
STNQConcl'' (NQEndFlow.lean:79) vs STNQConcl' (Step34PinsP.lean:53): 1 hunk(s): [(q.1 : ℝ))] -> [(s n))]
STXiBoot' (NQEndFlow.lean:95) vs STXiBoot (Step34Pins.lean:414): 1 hunk(s): [q.1.2)] -> [(s n))]
STIterR' (NQEndFlow.lean:134) vs STIterR (Step34Pins.lean:478): 1 hunk(s): [STXiBoot] -> [STXiBoot']
STOeqNQ'' (NQEndFlow.lean:124) vs STOeqNQ' (Step34PinsP.lean:70): 1 hunk(s): [STNQConcl'] -> [STNQConcl'']
STOeqQt' (NQEndFlow.lean:127) vs STOeqQt (Step34Pins.lean:462): 1 hunk(s): [STXiBoot] -> [STXiBoot']
STOeqQtNZ' (NQEndFlow.lean:130) vs STOeqQtNZ (Step34Pins.lean:465): 1 hunk(s): [STXiBoot] -> [STXiBoot']
STIterations' (NQEndFlow.lean:149) vs STIterations (Step34Pins.lean:497): 1 hunk(s): [STIterR] -> [STIterR']
STIterationsII' (NQEndFlow.lean:152) vs STIterationsII (Step34Pins.lean:500): 1 hunk(s): [STIterR] -> [STIterR']
STNQConclPT'' (NQEndFlow.lean:107) vs STNQConcl'' (NQEndFlow.lean:79): 1 hunk(s): [Prec] -> [PrecPT]
$ sed -n '974,977p;984,1000p' RBM3D/Induction/NQEndFlow.lean      # instance (1); instances (2)-(5): file lines 1002-1070 (17 examples in the file)
theorem inst_OeqNQPT'' :
    InstIngConcl (fun sz E s t => STNQConclPT'' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing STCaseI (fun sz E s t => STNQConclPT'' sz E s t) (stOeqNQPT''_holds 3) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos
…
example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiL sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 3 →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ))) :
    PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × {σ : Fin 3 → Bool // ∃ k, σ k = σ (finRotate 3 k)} ×
        (Fin 3 → Zd 3 (sz0.L n)))
      (fun n q ω => ‖Lloop sz0 n (STflowE z0 n) (q.1 : ℝ) q.2.1.1 q.2.2 ω -
        STKloop sz0 n (STflowE z0 n) (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz0.Bctl n (q.1 : ℝ)) ^ 3)
      (fun n q _ => (sz0.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 2 (fun _ => 1) (fun _ => 1) (sz0.Bctl n (sInst n)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqNQPT''
  exact hC (stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0)
    (stKward_of_flow sz0 (by norm_num) (by norm_num) flow_z0) hLK hStep2 3 1 (by norm_num) le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp
$ registry pre-check: scratch `import RBM3D` [+ `import RBM3D.Induction.NQEndFlow`] + `#assert_rbm_axioms`, `lake env lean`
# before = registry of b35643d, no new module (file swapped back temporarily from 04:06:26 UTC, then restored: `git status` 0 lines); exit 0
axiom audit: 7169 theorems, 2406 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 144 (borrowed 1, owed 98, structural 33, refuted 6, superseded 6).
registry: 2 borrowed + 149 owed + 93 structural + 7 refuted + 6 superseded; 113 registered premise(s) carry nothing yet
# after = branch HEAD (run finished 04:14:05 UTC); exit 0
axiom audit: 7175 theorems, 2418 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 144 (borrowed 1, owed 94, structural 33, refuted 6, superseded 10).
registry: 2 borrowed + 151 owed + 93 structural + 7 refuted + 11 superseded; 120 registered premise(s) carry nothing yet
# the seven primes are registered (listed under "carry nothing yet"): STOeqNQ'', STXiBoot', STOeqQt', STOeqQtNZ', STIterR', STIterations', STIterationsII'
$ git merge-tree --write-tree main HEAD     # main = 9403c24
ddf4dcede6b7… (exit 0, no conflict)
$ name-clash grep (grep -rn -F over RBM3D/ and RBM3D.lean; 20 names: the 18 new public names, `NQEndFlowInst`, prefix `nqFlow_`)
9403c24 /Users/junyin/Lean_proof/RBM3D -> STNQConcl'':0 STOeqNQ'':0 STXiBoot':0 STOeqQt':0 STOeqQtNZ':0 STIterR':0 STIterations':0 STIterationsII':0 STNQConclPT'':0 STOeqNQPT'':0 stOeqNQPT''_holds:0 stOeqNQ''_of_stOeqNQ':0 stXiBoot'_of_stXiBoot:0 stOeqQt'_of_stOeqQt:0 stOeqQtNZ'_of_stOeqQtNZ:0 nqFlowLam:0 nqFlowPhiC:0 NQEndFlowInst:0 inst_OeqNQPT'':0 nqFlow_:0
8c1a9b5 /Users/junyin/Lean_proof/RBM3D-wt/T2246 -> STNQConcl'':0 STOeqNQ'':0 STXiBoot':0 STOeqQt':0 STOeqQtNZ':0 STIterR':0 STIterations':0 STIterationsII':0 STNQConclPT'':0 STOeqNQPT'':0 stOeqNQPT''_holds:0 stOeqNQ''_of_stOeqNQ':0 stXiBoot'_of_stXiBoot:0 stOeqQt'_of_stOeqQt:0 stOeqQtNZ'_of_stOeqQtNZ:0 nqFlowLam:0 nqFlowPhiC:0 NQEndFlowInst:0 inst_OeqNQPT'':0 nqFlow_:0   # branch: the two writable files excluded (12 lines of Test/Axioms.lean mention the names)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/StoppedEndDefs.lean
 RBM2D/Induction/StoppedEndDefs.lean | 598 ++++++------------------------------
 1 file changed, 90 insertions(+), 508 deletions(-)
$ git diff --stat main...HEAD
 RBM3D/Induction/NQEndFlow.lean | 1095 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |   19 +-
 2 files changed, 1108 insertions(+), 6 deletions(-)
```
Narrative (all statements checkable in the file / the outputs above):
1. Files: `RBM3D/Induction/NQEndFlow.lean` (new, 1095 lines: 12 definitions, 6 public theorems, 28 private theorems + 1 private def, 17 examples) and `RBM3D/Test/Axioms.lean` (+13/-6); `git diff --stat main...HEAD` shows only these. No `sorry`/`admit`/`native_decide`/`axiom` and no `set_option maxHeartbeats` (grep: none). The module build prints no warning or error for the file.
2. Registry (Case A, `supersededProps` exists at `b35643d`): `STOeqNQ'`, `STOeqQt`, `STOeqQtNZ`, `STIterations`, `STIterationsII` moved from `owedProps` to `supersededProps` (ticket comment), the seven primes added to `owedProps`; `STOeqNQ`, `STXiBoot`, `STIterR` kept. Pre-check: exit 0, `found` unchanged at 144, no unregistered premise.
3. Pins: the 12 definitions equal check section 2 (script) and differ from the merged texts by the printed one-token hunks only. The three bridges between `STIngR` pins share one private lemma `nqFlow_ingR_mono` (:250); `stNQConcl''_of_stNQConcl'` is private (as `stNQConcl'_of_stNQConcl`) with its statement pinned by the `example` at :282.
4. `stOeqNQPT''_holds` (:921): `𝔠d = min (min 𝔠d_G 𝔠d_L) (1/(2d))` with the constants of `gridGoodN_holds d`, `nqLinGood_holds d` at the same `(κ, ε, 𝔡, C_d)`; `d 𝔠d ≤ 1/2 < 1` feeds `st_window`; `STConStInd` passes to `𝔠d_G`, `𝔠d_L` (`nqFlow_conStInd_exp_mono` :295); `GridGoodNConcl` is re-instantiated on every window `[s, v]` (`st_conStInd_sub`, `nqFlow_step2_restrict` :309); the premises of `nqGridEndLinN` come from `v3_premises_of_stFlow` (at `κ/2`, `ε/2`) and `st_window`; then `perTimeDomAt_iff_forall_section` and `nqFlow_section` (:826).
5. `nqFlow_section`: `v n = u n` where `s n < u n`, `v n = t n` elsewhere (so `s < v ≤ t`); `nqFlow_core` (:642) runs at `v` with the controls `XL m n (v n)`, `XLK m n (v n)` (`nqFlow_restrict_pair` :326); at the collapsed indices `u n = s n` the bound is `STLK s` at length `n_` with `ζ ≥ 1` (`nqFlow_bootRHS_one_le` :804).
6. `nqFlow_core`: the failure event of the terminal bound lies in the union of four events of probability `≤ N^{-(D+2)}`: the walk leaves `GoodSetN` (`GridGoodNConcl` at `Λ_s`, `Φc`, `q := p`, `C := C_K + 2`), leaves `GoodLinN` (`NQLinConcl`), an initial loop exceeds `N^{ε₁} B_s^{n_}` (`STLK s`, `map_pathH_eq` at `j = 0`), or lies in `Gᶜ` of `nqGridEndLinN` (`ε₀ = τ/2`, `D₁ = D + 2`); `4N^{-(D+2)} ≤ N^{-D}` for `N ≥ 2` (`nqFlow_four_pow_le` :571). Outside it `nqGridEndLinN` bounds the terminal loop by `N^{τ/2}(Λ_s^{1/2}+Φ₁+Φ₂+Φ₃) B_v^{n_} ≤ N^τ ζ B_v^{n_}`, transferred to `seqHflow` at `v n` by `map_pathH_eq` at `j = K n` and `gridTime_last`.
7. G1 in Lean: `nqFlow_lam_sqrt` (:361) is exact (`(nqFlowLam X B k p)^{1/2}` = first summand of `STbootRHS … B k p`); `nqFlow_level_le` (:402) gives `Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃ ≤ ζ` with `Λ_s = max 1 (nqFlowLam …)` (no factor `3`, no eventual); `nqFlow_phi3_le` (:377) gives `1 + Φ₃ ≤ Σ_{m=k-1}^{k+1} XL m`. The crude level is the sum `nqFlowPhiC`; `hX`, `hY` follow by `nqFlow_prec_of_le_right`; the `N^{C₀}` fallback was not needed.
8. Deviations from the ticket text (no statement changed): (i) target 5 names one lemma `nqFlow_section`; here `nqFlow_core` (non-collapsed `v`) and `nqFlow_section` (collapsed split), both private; (ii) `inst_OeqNQPT''` keeps `STKbound`, `STKward`, `STLK`, `STStep2Concl` as premises (shape of `inst_ing`); the example after it discharges `STKbound`, `STKward` by `stKbound_of_flow`, `stKward_of_flow`; (iii) extra examples for `stOeqQt'_of_stOeqQt` (case (i) data) and `stOeqQtNZ'_of_stOeqQtNZ` (the `szB`, `zB` data of `inst_OeqQtNZ`).
9. Port: the shape of RBM2D `gridEnd_to_flow` (`StoppedEndDefs.lean:297` at `c9a24cf`), `gridTerminal_transfer` (:254) and `StoppedEndDefs_union_le` (:448) is followed; the proofs are new (`nqGridEndLinN`, `gridGoodN_holds`, `nqLinGood_holds`, `Zd d L`, `Bctl`), no RBM2D text is copied; the RBM2D file has changed since `c9a24cf` (diff-stat above). Nothing was read from `../RBM1D`.
## (c) Verified Mathlib names used (module: name:line; resolved by Lean with `env.getModuleIdxFor?` and `findDeclarationRanges?`)
```
Mathlib.Analysis.SpecialFunctions.Pow.Real: Real.rpow_le_rpow_of_nonpos:565, Real.rpow_nonneg:163, Real.rpow_le_rpow:549, Real.rpow_le_rpow_of_exponent_le:616, Real.rpow_le_rpow_of_exponent_ge:643,
    Real.one_le_rpow:678, Real.mul_rpow:477, Real.div_rpow:488, Real.rpow_mul:415, Real.rpow_neg:259, Real.rpow_add:208, Real.rpow_two:471, Real.rpow_one:148, Real.one_rpow:154, Real.sqrt_eq_rpow:986,
    Real.rpow_pos_of_pos:116
Mathlib.Analysis.Real.Sqrt: Real.sqrt_le_iff:228, Real.sqrt_mul_self:152
Mathlib.Algebra.Order.GroupWithZero.Basic: div_nonpos_of_nonpos_of_nonneg:1109, div_le_div_of_nonneg_left:1270, div_le_div_of_nonneg_right:1193, div_le_iff₀:1132, lt_div_iff₀:1136
Mathlib.Algebra.Order.Field.Basic: div_le_one:43
Mathlib.Algebra.Order.BigOperators.Group.Finset: Finset.single_le_sum:265, Finset.sum_nonneg:151
Mathlib.Algebra.BigOperators.Group.Finset.Basic: Finset.sum_insert:48, Finset.sum_singleton:74
Mathlib.Algebra.Order.Floor.Semiring: Nat.ceil_lt_add_one:356, Nat.le_ceil:177
Mathlib.Algebra.Order.Floor.Defs: Nat.ceil_pos:160
Mathlib.MeasureTheory.Measure.Real: MeasureTheory.ofReal_measureReal:64
Mathlib.MeasureTheory.OuterMeasure.Basic: MeasureTheory.measure_union_le:88
Mathlib.MeasureTheory.Measure.Map: MeasureTheory.Measure.map_apply:169
Mathlib.MeasureTheory.MeasurableSpace.Defs: MeasurableSet.iUnion:104
Mathlib.MeasureTheory.Constructions.BorelSpace.Order: measurableSet_lt:245
Mathlib.MeasureTheory.Group.Arithmetic: Measurable.sub_const:258, Measurable.div_const:258
Mathlib.Basic.ENNReal.Real: ENNReal.ofReal_add:52, ENNReal.ofReal_le_ofReal:136
Mathlib.Order.Filter.AtTopBot.Tendsto: Filter.Tendsto.eventually_ge_atTop:38
Mathlib.Data.Set.Operations: Set.mem_ofPred_eq:78
Mathlib.Analysis.Matrix.MeasurableSpace: Measurable.of_eval_matrix:33
```
Tried first and found deprecated by the build (replaced in the file): `if_pos` (now the `↓reduceIte` simproc), `Set.mem_setOf_eq` (now `Set.mem_ofPred_eq`). A scratch file with `import Mathlib` fails here (`Mathlib.olean` is not built); the file imports project modules only.
## (d) Open issues and paper-delta candidates
- `T2246a` (R2*): the Lean pins `STNQConcl''`, `STXiBoot'` (and `STIterR'`, `STOeqQt'`, `STOeqQtNZ'`, `STIterations'`, `STIterationsII'`, `STOeqNQ''` over them) state the martingale summand `B^{-1/(4p)} (Ξ^{(L)}_{2n-1})^{1/2} (Ξ^{(L)}_{4p})^{1/(4p)}` of `(am;asoiuw)` `3_5:1143-1148` and `(am;asoi222)` `3_5:1366` at `B_{s,0}` (`sz.Bctl n (s n)`) in place of `B_{t,0}` / `B_{u,0}`: weaker than the printed bound (`B_s ≤ B_u`, negative exponent). The ticket asks that it be listed with T2207d (the case-(i) `B_{u,0}` of `(eq:alternatecase1)` `3_5:1676-1690`, numbered at this merge, DECISIONS §80 (3)).
- `T2246b`: `GridGoodNConcl` takes its controls over the window `[s, t]` of its own instance; the proof applies `gridGoodN_holds` on `[s, v_n]` (`v_n ≤ t_n`) and derives `(con_st_ind)` and `STStep2Concl` on `[s, v]` (`st_conStInd_sub`, `nqFlow_step2_restrict`): a Lean device, no paper counterpart.
- `T2246c`: the crude level of `GoodSetN` is taken as the sum `Σ_{m=1}^{k+1}(X_m + Y_m)` of the controls (`nqFlowPhiC`; `nqGridEndLinN` quantifies over every crude level); a Lean device, no paper counterpart.
- Observation (registry): a public conditional bridge counts as a proof of its conclusion head in `scanPremises` (`Test/Axioms.lean`), so `STOeqNQ''`, `STXiBoot'`, `STOeqQt'`, `STOeqQtNZ'` are not reported as unregistered premises when a later theorem assumes them; they are classified through `owedProps`, as `STOeqNQ'` was by `stOeqNQ'_of_stOeqNQ`. No action here.
- Observation (hub merge): `RBM3D/Test/Axioms.lean` / `RBM3D.lean` changed on `main` after `b35643d` (`git log --oneline b35643d..main -- RBM3D/Test/Axioms.lean RBM3D.lean` lists the merges T2237 T2243 T2248 T2247 T2242); `git merge-tree --write-tree main HEAD` at main = 9403c24 reports no conflict, so the registry hunks apply as a merge (H23 b), not by overwriting the file with the branch version.
- Next: S3-12c2 consumes `stOeqNQPT''_holds` (lift to `STOeqNQ''`); S3-18b proves `STXiBoot'`, `STOeqQt'`; S3-22 `STOeqQtNZ'`; S3-24b `STIterR'`, `STIterations'`, `STIterationsII'`.
