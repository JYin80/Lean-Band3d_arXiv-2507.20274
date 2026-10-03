Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 08:04:43 UTC 2026

Notation: `rho = W^eps`, `r = (g^2+1-s)/(g^2+1-t)`, `P = (1-s)/(1-t)`, `R1 = rho*l_s` (window), `R2 = rho^2*l_s` (S_far/S_near radius), `Xi = (t-s) mu S Theta_t`, `u = 1+Xi`, `nu = #{|y|_1<R1}`. Sources: `A_deterministic_estimates.tex:155-199`; pins `RBM3D/Evolution/Pins.lean:109-122` (`EKSumDecay2`), `Propagator/Pins.lean:58` (`Prop6Diff1`); `Evolution/XiPins.lean:281-303`; `Kernel/SumDecay.lean:149` (`latticesum_d3`, `latC k * log L / R^k`, `R : N`, strict `R < dist`).

### (i) Exponent table (route of the ticket; rows 1-11 close; row 12 is the failing step)

| # | quantity | value / count | constraint, where it enters | slack |
|---|---|---|---|---|
| 1 | non-alternating `sigma` | `ekSumDecayNAL_holds` gives `W^(C eps) r^(n-1)||A|| + W^(-D+C) <= ... r^n` (`r >= 1`) | needs `Prop5Short` (an antecedent of the pin); `C = max(C_alt, C_NAL)` | none needed |
| 2 | alternating `sigma` (`mu_i = m*conj m = 1`, all `Xi^(i)` equal) | `UN A = sum_{S subset [n]} T_S`; `T_S` with `S != empty` (a `delta` index): anchored sum, `r^(n-|S|) rho^(2(n-|S|)) <= rho^(2n) r^n` | `ek_core_bound`, `ek_UN_anchor_bound` pattern with row sum 1; `EKXiBall` (`Lambda'=rho`, `R1 <= rho l_s`) | none |
| 3 | `S_near` (`min_i |b1-a_i| <= R2`) | `sum_(S_near) |Xi(a1,b1)| <= n C_X rho^4 r` (n balls, `EKXiBall`, `Lambda'=rho^2`, `R=R2 <= Lambda' l_s`); other indices `C_X rho^2 r` each | `rho >= 1` | exponent `2(n+1)` (paper `(sum_res_deriv_red2)`, `W^(2(n+1)eps)`) |
| 4 | `S_far` factor `i notin B`, `i>=2` | `<= C 3^d rho^(4-d) r` (`kappa_X=(1-s)/(g^2+1-t) <= r/l_s^2`, `|a_i-b1| > R2`, `(3 R1)^d` window points) | `d>=3`: `rho^(4-d) <= rho` | `d=3`: `rho^1`; `d>=4`: `<= 1` |
| 5 | `S_far` factor `i in B`, `i != i2` (`Delta Xi`) | `<= C6 3^d rho^(3-d) r <= C6 3^d r` | `Prop6Diff1(c=1/2)` at `r_ = b_i-b1`, `|a'-b1| >= |a_i-b1|-1 > R2-1` (`S^B` radius 1): need `R2-1 >= 2 R1`, i.e. `rho(rho-2) l_s >= 1`; `Delta Xi` carries `(t-s)/(g^2+1-t) <= kappa_X` | needs `rho >= 2.42`; have `rho >= 4`: `rho(rho-2)=8 >= 1` (8x) |
| 6 | special index `i2 in B` and index 1 | `kappa_X^2 (rho l_s)^(d+1) latC(d-3) log L (R2/2)^-(d-3) <= C r^2 rho^(7-d) log L` (`kappa_X^2 <= r^2 l_s^-4`, `(rho l_s)^(d+1) R2^-(d-3) = rho^(7-d) l_s^4`) | `R = floor(R2) >= R2/2 >= 1`; `log L <= rho` (hypothesis) | `d=3`: `rho^4` times `log L <= rho` |
| 7 | `rho`-power of `f(B)`, `d=3` | `(n-2)*1 + 4 + 1(log L) = n+3`; general `d>=3`: `<= (n-2)(4-d)_+ + 8-d <= n+3` | paper `n+5`; design (a) row 13 `n+5-d` excl. log = `n+6-d`; **I prove `n+3`** (<= both) | 2 below paper's `n+5` |
| 8 | `r`-power | `r^(n-2)` (others) `* r^2` (special+index 1) `= r^n` | `r >= 1` | none |
| 9 | `C_n` | `m_n = min{m: 4^m > K_n}`, `K_n` collects `C_X, C_6, 3^d, latC, n, 2^n`; `C = m_n + 2n+2` (near `rho^(2n+2)`, tail `W^(-D) P^n <= W^(-D+n)`) | `4 <= W^eps`; `C >= n`; `C` indep. of `eps, D, L, g` | `O(n)` |
| 10 | `W^-1 <= (1-t)/(1-s)`; `t <= 1-g^2/L^2` | `P <= W` only for tails; `g^2/L^2 <= 1-t` for `EKXiDecay/EKXiBall` | — | instance 0.04 vs 0.2; 0.9 vs 0.99 |
| 11 | `log L <= W^eps`, `log L >= 1` (`L>=3`) | used once, row 6 | `rho >= 4` | `1.61 <= 5` at the instance |
| 12 | **leading term of `f(B)` (empty `Delta`-set) and window complement** | sum-zero kills `Xi(a1,b1) prod_(i>=2) Xi(a_i,b1) * sum_(b') A(b1,b')` only over **all** `b'`; restricted to the window it leaves `- sum_(b' notin Win) A`, bounded by `W^-D * L^(d(n-1))`; the paper (`A_deterministic_estimates.tex:186-190`) carries it as `W^(-D+n)` with no `L`-count | (my analysis) needs `L^(d(n-1)) <= W^K` (`K` before `C`); the pin has only `log L <= W^eps` | **fails: see (ii) block 3-4** |

### (ii) Instances and checks (python3/numpy, exact `Theta` by Fourier sum, eigenvalue `(1-s mu lam)/(1-t mu lam)`, `lam=(1+2g^2 sum cos)/(1+6g^2)`; no Lean)

Command: `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2042 && python3 pf2042.py` (sources `cx.py`, `grid.py`, `pf2042.py` there). Output, verbatim:
```
== 1. ticket instance (compiled-instance data): d=3 L=5 g=1/2 W=25 eps=1/2 D=2 s=1/2 t=9/10 m=i kappa=1/2 Lam=1
{'rho_ge_4': True, 'logL_le_rho': True, 'Winv_le': True, 't_le': True, 's_le_t': True, 'ell_s': 1, 'R1': 5.0, 'far_premise_only_if_dist_ge': 5.0, 'ekAz_support_dist': 1}
 n=2 sigma=+-: ||UN ekAz||=1.69287  r^n=4.5918  ratio=0.3687  (RHS = 25^(C/2) r^n + 25^(C-2) >= 4.592 for every C>0)
 n=3 sigma=+--: ||UN ekAz||=1.74486  r^n=9.8397  ratio=0.1773  (RHS = 25^(C/2) r^n + 25^(C-2) >= 9.840 for every C>0)
== 2. counterexample class A(b1,b2)=h(b1)[1_{|b2-b1|<R1} - nu/(L^3-nu) 1_{|b2-b1|>=R1}], h=1_{|b1|>=2R1}; closed form vs brute force u A u^T (n=2, sigma=+-, s=0, g=1/2, Q=3, R1=3)
 L=7: sum_b2 A = 0 (asserted) |A|max=1.0  brute UN A(0,0)=-9.25703486  closed form=-9.25703486
 L=9: sum_b2 A = 0 (asserted) |A|max=1.0  brute UN A(0,0)=-6.40196118  closed form=-6.40196118
== 3. legal hypotheses at L=129, g=1/2, s=0, t=1-g^2/Q^2 (ell_t=Q, ell_s=1), W=(1-s)/(1-t)=4Q^2, rho=W^eps=5, R1=5, kappa=1/2<=Im m=1
 Q   W      eps     [log L<=rho, (1-t)/(1-s)>=1/W, t<=1-g2/L2, 4<=rho]  nu   far-density  D_max  r     ||UN A||   ||UN A||/r^2  ||Xi||_2^2/Q
  6    144 0.3238 (True, True, True, True)  129 6.01e-05 1.956 4.865     73.38      3.10    2.072
 10    400 0.2686 (True, True, True, True)  129 6.01e-05 1.622 4.950    437.33     17.84    2.243
 14    784 0.2415 (True, True, True, True)  129 6.01e-05 1.458 4.975   1057.49     42.73    2.319
 18   1296 0.2246 (True, True, True, True)  129 6.01e-05 1.356 4.985   1825.42     73.47    2.362
 22   1936 0.2127 (True, True, True, True)  129 6.01e-05 1.284 4.990   2657.20    106.73    2.391
 ||Xi(0,.)||_2^2/Q: L=257 Q=10,22,40 -> 2.243 2.390 2.447 ; continuum limit (1/(8 pi)) c^-3/2 /g = 2.516
== 4. refutation for fixed C (D=C+1, W=4Q^2, rho=ln L >= 4, L=(nu(1+W^D))^(1/3), LHS >= 2.2Q - 1.05 N0(2 rho) - 1 [drops the factor nu], RHS = 25 rho^C + 1):
 C  D  Q*           W            log10 L   rho      nu        LHS_lb      RHS        ratio
 1  2      174.5   1.218e+05     4.45   10.258      1561       287.2       257.4   1.12
 2  3       5933   1.408e+08     9.52   21.928     13287   1.288e+04   1.202e+04   1.07
 3  4  9.271e+05   3.438e+12    18.39   42.334    102425   2.039e+06   1.897e+06   1.08
 4  5  3.105e+08   3.857e+17    31.21   71.855    487487   6.831e+08   6.665e+08   1.02
 6  7   2.13e+14   1.815e+29    70.52  162.386   5721625   4.687e+14   4.584e+14   1.02
== 5. intended class (A supported in |b1-b2|<R1=4, sum-zero per b1, ||A||<=1): exact sup over real A by sorting (n=2, sigma=+-, s=.5, a1=0, |a2|<=6), LP/r^2
 g=0.1 t=1-g2/L2: L=5: 13.87  L=9: 20.99  L=13: 24.67  
 g=0.5 t=1-g2/L2: L=5: 16.36  L=9: 25.41  L=13: 30.83  
```
Reading of the output.
- Block 1: at the ticket's compiled-instance data every hypothesis of `EKSumDecay2 3 2 1 (1/2)` holds (`prop5Decay_holds` `Prop5Hold.lean:784`, `prop5Short_holds` `Prop5Short.lean:400`, `prop6Diff1_holds` `Prop6Hold.lean:353` discharge the antecedents; `ekAz` has support `|b1-b2|<=1 < R1 = 5`, so `EKFastDecay` holds; `EKSumZero` holds). The bound holds with room (`ratio` 0.37, 0.18). Instance is nondegenerate (`L=5`, `W^eps=5`).
- Block 2: the closed form of `UN A` for the class below agrees with brute-force `u A u^T` to 8 digits (`n=2`).
- Block 3 (legal data, `L=129`, all four hypotheses `log L <= rho`, `(1-t)/(1-s) >= 1/W`, `t <= 1-g^2/L^2`, `4 <= rho` `True`; `kappa=1/2 <= Im m = 1`; `Lambda=1`; `D = 1.25 < D_max`): `A(b1,b2) = h(b1)[1_(|b2-b1|<R1) - nu/(L^3-nu) 1_(|b2-b1|>=R1)]`, `h = 1_(|b1|>=2 R1)`. `||A|| = 1`; `sum_(b2) A = 0` for every `b1` (`EKSumZero`); far entries `= nu/(L^3-nu) = 6e-5 <= W^-D` (`EKFastDecay`). Here `||UN A||/r^2` rises from 3.1 to 106.7 over `Q = 6..22` at fixed `rho = 5`, `r ~ 5` (not yet in the asymptotic regime: `R2 = 10` cuts the near part); the mechanism is `UN A(0,0) >= sum_(|x|>=2R1) Xi(x)^2 - nu P^2/L^3` (`Xi >= 0`, window contains `y=0`, `nu P^2/L^3 < W^(2-D)`), and `||Xi||_2^2 ~ 2.5 Q` (last column; continuum limit 2.516), i.e. linear in `l_t = Q`, not bounded by `rho^C r^n`.
- Block 4: for every fixed `C` (the pin's `exists C` comes first) take `D = C+1`, `g=1/2`, `s=0`, `1-t = g^2/Q^2`, `W = 4Q^2` (`(1-t)/(1-s) = 1/W`), `L = (nu(1+W^D))^(1/3)` (density `nu/(L^3-nu) <= W^-D`), `rho = ln L` (`=W^eps`, `eps = ln rho/ln W in (0,1)`), `W^(-D+C) = 1/W`: then `||UN A|| >= 2.2 Q - 1.05 N0 - 1 > 25 rho^C + 1 >= W^(C eps) r^2 ||A|| + W^(-D+C)` for `Q >= Q*` (table, `rho = O(ln Q)`, so `Q/(ln Q)^C -> infinity`). Table is an extrapolation (`||Xi||_2^2 >= 2.2Q` verified to `Q=40`, limit 2.52Q; `N0` = near part at `t->1`, `L=257`); it also drops a factor up to `nu` from the window sum `Wn(x) >= Xi(x)`, so the true `Q*` is smaller. It is not a proof of the lower bound on `Theta`; the exact numbers of block 3 and the closed form of block 2 are.
- Block 5: for the class the paper's proof handles (`A` supported in the window, sum-zero per `b1`), the exact sup over `||A||<=1` shows growth `~ log L` (about 10-15 per `log L` unnormalised at `rho=4`, `s=0.5`; T2016 normalised by `rho^4 r^2` gave slope about 1), and the route rows 1-11 close there.
- External hypotheses: `Prop5Decay`, `Prop5Short`, `Prop6Diff1` are proved Props (above), no limit computation owed; row 5 range check is arithmetic.

### Verdicts
- `ekSumDecay2_holds (d n Lambda kappa) : EKSumDecay2 d n Lambda kappa`: **FAIL** for `d=3, n=2, Lambda >= 1/2, kappa <= 1` (so the `forall d n` statement is unprovable). Reason: the pin has no relation between `L` and `W` except `log L <= W^eps` (does not repair it: the family in block 4 satisfies it with equality), while `EKSumZero` sums over all of `b'` and `EKFastDecay` is pointwise `W^-D`; compensating mass spread over `L^d` far sites at density `<= W^-D` makes `A` window-non-neutral, and `||UN A||` then carries `l_t/l_s` (the `(sum_res_1)` loss), unbounded against `W^(C eps) r^n + W^(-D+C)`. Dispatcher decision needed (no pin change by me): candidates: add antecedent `L^d <= W^K` with `C` depending on `K` (row 12 then closes with `C >= n + K(n-1)`), or window-restricted sum-zero, or `l^1` far decay. Paper-delta candidate `T2042a`: `(eq:bddfA)` complement `W^(-D+n)` needs `L` polynomial in `W`. Not a `T2016a/b/f` item; the `n+5` vs `n+3` question is moot (row 7).
- With the pin repaired as above the route (rows 1-11) closes with `C = m_n + 2n + 2` (row 9); `Prop6Diff1` range needs `rho >= 2.42` (have 4), candidate `T2016b` stands.

## (a) Math preflight, restart under Amend 1 (DECISIONS §21) — Sat Oct  3 08:49:34 UTC 2026

Round-1 text above is kept (its verdict FAIL concerned the old pin). Amended pin (check file `docs/tickets/checks/T2042-check.lean`, `RBM.T2042Check.EKSumDecay2`): `∀ K>0` before `∃ C>0`, antecedent `(L:ℝ)^d ≤ W^K` after `Real.log L ≤ W^ε`; all other hypotheses and the conclusion are unchanged. Scratch: `scratchpad/T2042/pf2042b.py` (python3, no Lean), output `pf2042b.out`.

### (i) Row 12 redone (rows 1-11 unchanged; `K` enters only here and in the constant of row 9)

| # | quantity | value / count | constraint | slack |
|---|---|---|---|---|
| 12' | far complement of the window in the empty-`Δ` term (leading term, `sum-zero` over all `b'`) | `|Σ_{b'∉Win}A(b1,b')| ≤ L^d W^{-D}`; the other `n−1` indices `b_i` (i≥2) carry `Ξ(a_i,b1)` with no decay in `b_i`, so the complement count is `(L^d)^{n-1}`; `Σ_{b1}∏_i|Ξ(a_i,b1)| ≤ P·P^{n-1} = P^n` (max entry ≤ `ℓ¹` row sum of `Ξ` ≤ `(t−s)/(1−t) ≤ P`) | total `≤ W^{-D} L^{d(n-1)} P^n ≤ W^{-D} W^{K(n-1)} W^n` using the new antecedent and `P=(1-s)/(1-t) ≤ W` (`W⁻¹ ≤ (1−t)/(1−s)`) | closes with `C ≥ n + K(n−1)` (n=2: `2+K`; n=3: `3+2K`); at `K=2`: `C ≥ 4` (n=2), `C ≥ 7` (n=3); `C ≥ K` for all `n ≥ 2` |
| 9' | constant `C = C(n,K)` | `C = max(m_n + 2n + 2, n + K(n−1))` (row 9's `m_n+2n+2` for the near/tail parts, row 12' for the complement); independent of `ε, D, L, g, W`, depends on `n, K, d, Λ, κ` | `4 ≤ W^ε`, `C ≥ n` | the two parts are independent; `C` increasing in `K`; `W^{Cε}≥1` so enlarging `C` is harmless |
| 13' | new antecedent vs the rest | `L^d ≤ W^K` implies `log L ≤ (K/d) log W` but not `log L ≤ W^ε` (ε may be tiny), so the `log L ≤ W^ε` hypothesis (row 11) is still needed | — | unchanged |

`ℓ¹` row-sum input (script block A, exact `Ξ` by Fourier sum, `μ=±1`, 6 parameter sets): `Σ_b|Ξ(0,b)| ≤ P` in all 12 cases, worst ratio `0.9998` (`μ=+1`, `t→1`); `μ=−1` ratio ≤ 0.08. Route: `ρ`-power `n+3` (≤ paper's `n+5`) as in row 7; paper `(eq:bddfA)`'s `W^{-D+n}` becomes `W^{-D+n+K(n−1)}` (candidate `T2042a`, signed).

### (ii) Block-4 family violates the antecedent; the instances satisfy every hypothesis

Command: `cd <scratchpad>/t2042 && python3 pf2042b.py`. Verbatim output:
```
== B. amended row 12 at the ticket instance (d=3,L=5,W=25,K=2,s=.5,t=.9,g=.5): complement <= W^-D L^(d(n-1)) P^n  vs  W^(-D+C), C>=n+K(n-1)
 antecedent L^d=125 <= W^K=625: True;  P=5.0 <= W=25: True
 n=2: C_min=n+K(n-1)=4; L^(d(n-1)) P^n=3125.0 <= W^C_min=3.906e+05: True; (L^d)^(n-1) <= W^(K(n-1)): True
 n=3: C_min=n+K(n-1)=7; L^(d(n-1)) P^n=1953125.0 <= W^C_min=6.104e+09: True; (L^d)^(n-1) <= W^(K(n-1)): True
== C. block-3 data (L=129,g=.5,s=0,t=1-g2/Q2,rho=5): antecedent L^3<=W^K needs K>=K0; take K=3, n=2, C_min=n+K(n-1)=5; first RHS term W^(C eps) r^n ||A|| = rho^C r^2 (||A||=1)
 L^3=2146689 ; K=3 antecedent holds at every row below if W^3>=L^3:
 Q= 6 W=   144 K0=log(L^3)/log W=2.934 ant(K=3)=True  ||UN A||=    73.38  rho^C_min r^2=   73959.1  ratio=0.0010
 Q=10 W=   400 K0=log(L^3)/log W=2.433 ant(K=3)=True  ||UN A||=   437.33  rho^C_min r^2=   76585.6  ratio=0.0057
 Q=14 W=   784 K0=log(L^3)/log W=2.188 ant(K=3)=True  ||UN A||=  1057.49  rho^C_min r^2=   77333.9  ratio=0.0137
 Q=18 W=  1296 K0=log(L^3)/log W=2.034 ant(K=3)=True  ||UN A||=  1825.42  rho^C_min r^2=   77645.0  ratio=0.0235
 Q=22 W=  1936 K0=log(L^3)/log W=1.926 ant(K=3)=True  ||UN A||=  2657.20  rho^C_min r^2=   77803.2  ratio=0.0342
== D. block-4 family against the amended antecedent: L^3 = nu(1+W^D) >= W^D, so log_W(L^3) >= D = C+1; K_min(row)=log(L^3)/log W (parsed from pf2042.out block 4)
 C  D   log10 W   log10 L  K_min=3 logL/logW   violates antecedent for every K<=D? (K_min>=D)
 1  2      5.09     4.45      2.625            True
 2  3      8.15     9.52      3.505            True
 3  4     12.54    18.39      4.401            True
 4  5     17.59    31.21      5.324            True
 6  7     29.26    70.52      7.231            True
 For a given K the pin yields C(K); the adversary takes D > max(K,C(K)): then L^3 >= W^D > W^K, antecedent fails. For D<=K the far mass is <= L^d W^-D <= W^(K-D) <= W^(-D+C) when C>=K (C_min=n+K(n-1)>=K: n>=2).
 C_min>=K check, n=2,3,4, K=0.5,1,2,5: True
```
Reading.
- Block D: block-4 family (round 1) has `L^3 = ν(1+W^D) ≥ W^D` (this is what makes the far density `ν/(L^3−ν) ≤ W^{-D}`), so `log_W(L^d) ≥ D`. For fixed `K` the pin supplies `C(K)` first; the adversary then takes `D > max(K, C(K))` and `L^d ≥ W^D > W^K`: antecedent fails, family excluded. Table: all five rows have `K_min = log(L^3)/log W ≥ D = C+1` (2.625, 3.505, 4.401, 5.324, 7.231), so none satisfies `L^3 ≤ W^K` for any `K ≤ D`, in particular not `K=2`. For `D ≤ K` the far mass is `≤ L^d W^{-D} ≤ W^{K−D} ≤ W^{-D+C}` (needs `C ≥ K`, true for `C ≥ n+K(n−1)`).
- Block B (ticket instance `d=3, L=5, g=1/2, W=25, ε=1/2, D=2, s=1/2, t=9/10, m=i, K=2`, `n ∈ {2,3}`): antecedent `125 ≤ 625` holds; round-1 block 1 checked the other hypotheses (`4 ≤ W^ε=5`, `log 5 ≤ 5`, `W⁻¹=0.04 ≤ 0.2`, `t=0.9 ≤ 0.99`, `ekAz` fast decay and sum-zero) and the bound (ratios 0.37, 0.18). Complement term at `C_min`: `3125 ≤ 3.9e5` (n=2), `1.95e6 ≤ 6.1e9` (n=3). Instance nondegenerate (`L=5`, `W^ε=5`, `n=2,3`).
- Block C (round-1 block-3 legal data, `L=129`): with `K=3` the antecedent holds in every row (`K0 ≤ 2.934`); the formerly violating ratio `‖UN A‖/(ρ^{C_min} r^2)` is `0.001..0.034` (`C_min = 5`), i.e. consistent with the amended pin. Block-3 growth in `Q` is then absorbed by `K=3` (consistent, not a proof).
- External hypotheses `Prop5Decay`, `Prop5Short`, `Prop6Diff1` are proved Props (`prop5Decay_holds`, `prop5Short_holds`, `prop6Diff1_holds`); no limit computation owed.

### Verdicts (amended ticket)
- `ekSumDecay2_holds (d n Λ κ) : EKSumDecay2 d n Λ κ` (amended `def`): **PASS**. Hypothesis set satisfiable at the instance (`K=2`), counter-family excluded by `L^d ≤ W^K`, exponent closes with `C = max(m_n+2n+2, n+K(n−1))`, `ρ`-power `n+3`; `Prop6Diff1` range needs `ρ ≥ 2.42` (have 4). Remark for 1b: the complement bound uses `Σ_b|Ξ(a,b)| ≤ P` (entrywise `|Θ_t| ≤ (1−tS)^{-1}`), and the `(L^d)^{n−1}` count.

## (a′) Preflight corrections — Sat Oct  3 09:39:02 UTC 2026
No error of section (a) that changes a verdict. One divergence of intent: row 7 / row 13' say "I prove `n+3`"; the exponent in the file is `m₁+2n+2` (docstring of `ekSumDecay2_holds`, lemma `ekSZ_final_arith`): every non-special window sum is bounded by `ρ² r` (`ekSZ_concrete`: `hX`, `hΔ`, `Snon`), the pin's `C` is existential, no statement changes.

## (b) Script output — Sat Oct  3 09:41:34 UTC 2026 (branch `t/T2042`, worktree `RBM3D-wt/T2042`, commit `dde1751`, base `cca94be`; model claude-sonnet-5-5)
### b1 Builds, registry pre-check (DECISIONS §20), axioms
```
commit: dde1751
Sat Oct  3 09:41:09 UTC 2026
$ lake build RBM3D.Evolution.SumDecayZero
Build completed successfully (3421 jobs).
$ lake build   (full library; root #assert_rbm_axioms; the root does not import the new module yet)
info: RBM3D.lean:79:0: axiom audit: 1345 theorems, 469 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 16 (borrowed 2, owed 1, structural 13).
Build completed successfully (3739 jobs).
$ lake env lean precheck.lean  (import RBM3D; import RBM3D.Evolution.SumDecayZero; #assert_rbm_axioms)
axiom audit: 1346 theorems, 469 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 16 (borrowed 2, owed 1, structural 13).
exit: 0
$ lake env lean axs.lean
'RBM.ekSumDecay2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.ekSumDecay2_holds : ∀ (d n : ℕ) (Λ κ : ℝ), RBM.EKSumDecay2 d n Λ κ
Sat Oct  3 09:41:23 UTC 2026
```
### b2 The amended pin, its three edits in `Pins.lean`, and the target (statements extracted by script)
```
Sat Oct  3 09:37:45 UTC 2026
$ python3 cmp.py   (def EKSumDecay2: docs/tickets/checks/T2042-check.lean vs RBM3D/Evolution/Pins.lean)
verbatim equal: True
$ git diff main...t/T2042 -- RBM3D/Evolution/Pins.lean | grep "^[+-]" | grep -v "^+++\|^---"   (the only edits of Pins.lean)
-`T2016a`). -/
+`T2016a`).  `L^d ≤ W^K` (candidate `T2042a`, DECISIONS §21) is the paper's `(Main_DEL_COND)` read
+with `K = 1/𝔠`; `C` depends on `K`. -/
+    ∀ K : ℝ, 0 < K →
+        (L : ℝ) ^ d ≤ W ^ K →
-    (by norm_num)
+    (by norm_num) 2 two_pos
-    ek_log5 (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I
+    ek_log5 (by norm_num [Real.rpow_two]) (1 / 2) (9 / 10) (by norm_num) (by norm_num)
+    (by norm_num) (by norm_num) Complex.I
$ python3 extract.py   (statements extracted from the files)
RBM3D/Evolution/SumDecayZero.lean:1411: theorem ekSumDecay2_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecay2 d n Λ κ
--- RBM3D/Evolution/Pins.lean:110-123 (the amended pin; verbatim equal to the check file's def, script above)
def EKSumDecay2 (d n : ℕ) (Λ κ : ℝ) : Prop :=
  Prop5Decay d Λ → Prop5Short d Λ κ → Prop6Diff1 d Λ κ (1 / 2) →
    3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
    ∀ K : ℝ, 0 < K →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε →
        (L : ℝ) ^ d ≤ W ^ K →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          EKFastDecay g s W ε D A → EKSumZero A →
          ‖UN d L g (EKsgn m σ) s t A‖ ≤
            W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)
```
### b3 Compiled nonempty instances (statements extracted by script; all five `example`s are in the module built in b1)
```
--- instances in SumDecayZero.lean (statement parts; proofs are in the file):
RBM3D/Evolution/SumDecayZero.lean:1713-1718
  /-- **Instance of `ekSumDecay2_holds`**, `n = 2`, `σ = (+,-)`, `K = 2`, `A = δ₀ ⊗ (δ₀ - δ_e)`. -/
  example : ∃ C : ℝ, 0 < C ∧
      ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) ekSZAz2‖ ≤
        (25 : ℝ) ^ (C * (1 / 2)) *
          (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2 * ‖ekSZAz2‖
        + (25 : ℝ) ^ (-2 + C) := by
RBM3D/Evolution/SumDecayZero.lean:1728-1734
  /-- **Instance of `ekSumDecay2_holds`**, `n = 3`, `σ = (+,-,+)`, `K = 2`,
  `A = δ₀ ⊗ (δ₀ - δ_e) ⊗ δ₀`. -/
  example : ∃ C : ℝ, 0 < C ∧
      ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false, true]) (1 / 2) (9 / 10) ekSZAz3‖ ≤
        (25 : ℝ) ^ (C * (1 / 2)) *
          (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 3 * ‖ekSZAz3‖
        + (25 : ℝ) ^ (-2 + C) := by
$ grep -n "^example" SumDecayZero.lean   (all examples of the file are compiled by the build above)
1695:example : ekSZAz2 ![0, 0] = 1 ∧ ekSZAz2 ![0, ekSZe] = -1 := by
1699:example : ekSZAz3 ![0, 0, 0] = 1 ∧ ekSZAz3 ![0, ekSZe, 0] = -1 := by
1705:example (n : ℕ) (hn : 2 ≤ n) :
1714:example : ∃ C : ℝ, 0 < C ∧
1730:example : ∃ C : ℝ, 0 < C ∧
$ grep -n "theorem ekSZ_fastDecay[23]\|theorem ekSZ_sumZero[23]" SumDecayZero.lean   (private: the instance data discharge (deccA0), (sumAzero))
1667:private theorem ekSZ_fastDecay2 : EKFastDecay (1 / 2 : ℝ) (1 / 2) 25 (1 / 2) 2 ekSZAz2 := by
1674:private theorem ekSZ_fastDecay3 : EKFastDecay (1 / 2 : ℝ) (1 / 2) 25 (1 / 2) 2 ekSZAz3 := by
1682:private theorem ekSZ_sumZero2 : EKSumZero ekSZAz2 := by
1688:private theorem ekSZ_sumZero3 : EKSumZero ekSZAz3 := by
```
### b4 Names, scope, forbidden tokens, map of the file
```
Sat Oct  3 09:39:23 UTC 2026
$ grep -rn "ekSumDecay2_holds\|ekSZ" RBM3D RBM3D.lean --include="*.lean" | grep -v "Evolution/SumDecayZero.lean"   (worktree, commit dde1751)
$ git -C ../RBM3D grep -n "ekSumDecay2_holds\|ekSZ" main -- RBM3D RBM3D.lean   (current main, bac6c2f)
(no output = no clash)
$ grep -n "^theorem\|^def\|^lemma\|^abbrev\|^instance\|^structure\|^noncomputable def" SumDecayZero.lean   (public declarations)
1411:theorem ekSumDecay2_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecay2 d n Λ κ := by
private declarations: 44
$ grep -n "sorry\|admit\|native_decide\|^axiom" SumDecayZero.lean
(no output = none)
$ git diff --stat main...t/T2042   (commit dde1751; main moved to bac6c2f; merge base cca94be)
 RBM3D/Evolution/Pins.lean         |   10 +-
 RBM3D/Evolution/SumDecayZero.lean | 1746 +++++++++++++++++++++++++++++++++++++
 2 files changed, 1753 insertions(+), 3 deletions(-)
$ git status --short   (worktree)
(clean)
$ wc -l SumDecayZero.lean
    1746 RBM3D/Evolution/SumDecayZero.lean
Sat Oct  3 09:39:50 UTC 2026
$ grep -n "^private theorem ekSZ_\(anchor_dep\|UW_bound\|tail_bound\|fempty_bound\|fB_bound\|core\|card_win\|dXi_le\|lattice\|concrete\|arith_M\|arith_D\|final_arith\)\|^theorem ekSumDecay2_holds" SumDecayZero.lean
100:private theorem ekSZ_anchor_dep
151:private theorem ekSZ_UW_bound
188:private theorem ekSZ_tail_bound
238:private theorem ekSZ_fempty_bound
313:private theorem ekSZ_fB_bound
436:private theorem ekSZ_core
641:private theorem ekSZ_card_win
663:private theorem ekSZ_dXi_le
783:private theorem ekSZ_lattice
821:private theorem ekSZ_concrete
1167:private theorem ekSZ_arith_M
1234:private theorem ekSZ_arith_D
1309:private theorem ekSZ_final_arith
1411:theorem ekSumDecay2_holds
```
### b5 Narrative
- Result: `ekSumDecay2_holds (d n Λ κ) : EKSumDecay2 d n Λ κ` for the amended pin (b2); axioms: the three standard ones (b1); no hypothesis beyond the pin's antecedents. `Prop5Short` (named `_h5s`) and `1 < D` are not used by the proof; `κ ≤ Im m` enters through `Prop6Diff1`.
- The file (1746 lines, 1 public theorem, 44 private declarations, map in b4): Part I `ekSZ_core` is the combinatorics over an arbitrary finite type; Part II `ekSZ_concrete` checks its hypotheses on `Zd (k+3) L`; Part III is the arithmetic of `C`; Part IV the theorem and the instances.
- Route as proved. `UN A a = Σ_b ∏_i u_i A_b`, `u_i = δ + Ξ_i`; the sum-zero index is `i₀ = ⟨0,_⟩`; `ρ = W^ε`, `R = ρ ℓ_s`, `far x := ∀ j, ρR < |a_j - x|`; the row `u_{i₀}` is split `δ + w_near + w_far`.
  (1) `δ + w_near`: one `ek_core_bound` (anchor `i₀`, `Rk = 1 + Rn`, `Rn = n C_B ρ⁴ r` from `ekXiBall_holds` at `Λ' = ρ²`, one ball per `a_j`).
  (2) `w_far`: window / complement, complement cost `δ Q (1+Q)^{n-1}` (`ekSZ_tail_bound`); on the window `u_i = Ξ_i` (`hne`) and `Ξ_i(a_i,b_i) = Ξ_i(a_i,b_{i₀}) + ΔΞ_i`, expanded over the subsets `B ⊆ {i ≠ i₀}` (`Finset.prod_add`).
  (3) `B = ∅`: by `(sumAzero)` the window sum is minus the off-window sum, `≤ δ Q^n |X|^{n-1}` with `|X| = L^d` (`ekSZ_fempty_bound`).
  (4) `B ≠ ∅`: `ekSZ_anchor_dep` factorizes the window sum; each of the `n-2` other indices costs `Snon = 3^d (C_D + C₆) ρ² r`; the distinguished `j ∈ B` costs `Ψ = 3^d C₆ C_D latC(d-3) log L ρ⁴ r²` (`ekSZ_dXi_le` from `Prop6Diff1` at `c = 1/2`, needing `2|y-x|+1 ≤ |a-x|`, from `4R ≤ ρR`, `R ≥ 1`; then `latticesum_d3` via `ekSZ_lattice`; `log L ≤ ρ`).
- Hypotheses: `L^d ≤ W^K` enters only in `ekSZ_final_arith` (`(L^d)^{n-1} ≤ W^{K(n-1)}`); `W⁻¹ ≤ (1-t)/(1-s)` gives `1+Q = (1-s)/(1-t) ≤ W`; `4 ≤ W^ε` gives `ρ ≥ 4`, `4^m ≤ ρ^m`, `4^m ≤ W^m`.
- Constants: `C = (m₁+2n+2) + (m₂+n+4+K(n-1))` (docstring of `ekSumDecay2_holds`), depends on `(d,n,Λ,κ,K)` only. The `ρ`-power proved is `m₁+2n+2`: not the paper's `n+5`, not (a)'s `n+3`; `(sum_res_2_red)` carries `C_n`, so no new paper delta.
- Registry (DECISIONS §20): the pre-check exits 0 and finds 16 premises with and without the new module; `ekSZ_concrete`, the only lemma taking `EKFastDecay` and `EKSumZero` as hypotheses, is private, so `RBM3D/Test/Axioms.lean` is not edited.
- Ports: none. The RBM2D files named in the ticket (`Evolution/XiBounds.lean:598-783`, `Case4.lean`) and RBM1D were not opened; no diff-stat.
- Instances: `K = 2`, `L = 5, g = 1/2, W = 25, ε = 1/2, D = 2, s = 1/2, t = 9/10, m = I`; the three antecedents come from `prop5Decay_holds`, `prop5Short_holds`, `prop6Diff1_holds`; `(deccA0)` and `(sumAzero)` of the tensors are proved in the file; no hypothesis of the examples is left open. Non-vacuity: both tensors take the values `1` and `-1`; a far pair of indices exists for every `n ≥ 2` (b3).

## (c) Verified Mathlib names (`#check @Name` in the module's import context, script `names.lean`)
117 of 118 present; the miss `Matrix.Norms` is a namespace (`open scoped Matrix.Norms.Operator`). Qualified, present (96): Complex.I, Complex.I_im, Complex.norm_I, Complex.norm_real, Complex.ofReal_sub, Fin.ext, Fin.isValue, Fin.prod_univ_three, Fin.prod_univ_two, Fin.sum_univ_three, Finset.add_sum_erase, Finset.card_erase_le, Finset.card_erase_of_mem, Finset.card_le_card, Finset.card_le_card_of_injOn, Finset.card_powerset, Finset.card_univ, Finset.empty_mem_powerset, Finset.filter_filter, Finset.mem_filter, Finset.mem_of_mem_erase, Finset.mem_powerset, Finset.mem_sdiff, Finset.mem_univ, Finset.mul_prod_erase, Finset.mul_sum, Finset.ne_of_mem_erase, Finset.nonempty_iff_ne_empty, Finset.prod_add, Finset.prod_congr, Finset.prod_const, Finset.prod_empty, Finset.prod_eq_zero, Finset.prod_erase, Finset.prod_ite, Finset.prod_le_prod, Finset.prod_le_prod₀, Finset.prod_nonneg, Finset.prod_univ_sum, Finset.sdiff_empty, Finset.single_le_sum, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_congr, Finset.sum_const, Finset.sum_fiberwise, Finset.sum_filter, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_le_card_nsmul, Finset.sum_le_sum, Finset.sum_le_sum_of_subset_of_nonneg, Finset.sum_mul, Finset.sum_nonneg, Finset.sum_sub_distrib, Finset.univ, Fintype.card, Fintype.card_fin, Fintype.card_piFinset, Fintype.mem_piFinset, Fintype.piFinset, Fintype.piFinset_univ, Matrix.add_apply, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, Nat.cast_nonneg, Nat.cast_pow, Nat.cast_sub, Nat.floor_le, Nat.le_floor, Nat.lt_floor_add_one, Nat.zero_le, Real.exp, Real.exp_le_one_iff, Real.exp_pos, Real.log, Real.log_le_sub_one_of_pos, Real.log_nonneg, Real.norm_of_nonneg, Real.one_le_rpow, Real.rpow_add, Real.rpow_le_rpow_of_exponent_le, Real.rpow_mul, Real.rpow_natCast, Real.rpow_nonneg, Real.rpow_one, Real.rpow_two, Real.sqrt, Real.sqrt_eq_rpow, Real.sqrt_le_sqrt, Real.sqrt_sq, ZMod.val_zero.
Unqualified, present (21): pow_unbounded_of_one_lt, one_le_pow₀, pow_le_pow_left₀, pow_le_pow_right₀, inv_anti₀, inv_le_of_inv_le₀, pi_norm_le_iff_of_nonneg, norm_le_pi_norm, div_nonpos_of_nonpos_of_nonneg, norm_sum_le, norm_prod, norm_add_le, sub_add_sub_cancel, eq_neg_of_add_eq_zero_left, inv_div, le_div_iff₀, div_le_div_iff₀, div_eq_mul_inv, mul_pow, pow_add, pow_succ'.
Deprecated in this Mathlib (`Linter.isDeprecated` = true): `if_pos`, `if_neg`, `if_true`, `if_false`, `Finset.prod_le_prod'`. `Finset.prod_le_prod` is the monoid form `(∀ i ∈ s, f i ≤ g i) → ∏ f ≤ ∏ g`; the semiring form with `0 ≤ f i` is `Finset.prod_le_prod₀`.

## (d) Open issues and paper-delta candidates (written Sat Oct  3 09:40:44 UTC 2026)
- Cited, not re-proposed: `T2042a` (DECISIONS §21: the complement in `(eq:bddfA)` needs `L^d ≤ W^K`; here `C` carries `K(n-1)`), `T2016a` (`log L ≤ W^ε`, used as `log L ≤ ρ` in `Ψ`), `T2016b` (`4 ≤ W^ε`), `T2016f` (constants uniform in `g ∈ (0,Λ]`, `ℓ¹` windows). No new candidate.
- Open, for the dispatcher: (i) `Prop5Short` is an antecedent of the pin but unused by this proof, as is `1 < D`; dropping either is a pin amendment, not done. (ii) `ekSZ_core` and `ekSZ_dXi_le` are private; a consumer that wants them needs a follow-up that publishes them. (iii) (a) row 7 counts `ρ^{n+3}`; the file proves `ρ^{m₁+2n+2}`.
- Mathlib notes for `docs/mathlib-api.md`: the lists of (c); `Finset.prod_le_prod` against `Finset.prod_le_prod₀`; `if_pos`, `if_neg`, `if_true`, `if_false` are deprecated (use `↓reduceIte`).
