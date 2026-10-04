Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 05:12:45 UTC 2026

Notation: `P(r) := STprof(…, r) = W^{-d} 𝒯̃^ℓ_{t,D}(r)` (`Step2Defs.lean:75`), `ρ = r∧ℓ⁺`, `ℓ⁺ = max(ℓ_n,0)`, `u = 1-t`, `B(ρ) = Bparam`/`BparamR`, `N = sz.size`, `y² = N^{τ'}`, `η = etaT`, `Bctl = W^{-d}B_{t,0}` (`Defs/Sizes.lean:214`), `ℓ*=(log W)^{3/2}ℓ_t`, `ℓ†=(log W)^{7/4}ℓ_t`, `r=|a-b|` (`zdistInf`). Paper lines `3_5:n`.

### (i) Exponent table, proof map, cut

**Proof map of `(eq:MG_conclusion3)` (`3_5:829–888`).** `|EE_0| ≤ W^d Σ_{|c-c'|≤1}|𝓛⁶|` (`|SB|≤1`, support `|c-c'|≤1`; `emn2_ee_le` core, T2102); `k=1` is `k=0` at `((σ₂,σ₁),(a₂,a₁))`.
- M1 `3_5:829–836` near case `r ≤ ℓ†`: truncated `Ψ'_n(r) = min((W^{-d}B(r∧ℓ⁺))^{1/2}, W^{-ε₀'})` (min only to make the `∀ n` clauses of `STPsiClass` true; eventually inactive). Premises of `STEMn2Poly` at `(ε₀',Ψ')` all follow from the pin's (row 1–4): `STPsiClass` (rows 2); `STLWassm` from `STLWassmExp` at `D'' = 2+(d-2)/(𝔠d)` since `P_{D''}(r) ≤ W^{-d}B(ρ) = Ψ'(r)²` for ALL `r` (`𝒯≤B`, `W^{-D''}≤B`); `STInitialGT2.1` from the pin's at `ε₀ ≥ ε₀'`, `.2` from `STLWassmExp` + `P` antitone + `P(0)=Bctl` (`tailT_zero`, `tailW_antitone`); then `stEMn2Poly_holds` (`EMn2Poly.lean:838`) gives `η⁻¹Ψ'(0)Ψ'(r)⁴`, and `Ψ'(0)=Bctl^{1/2}`, `Ψ'(r)² ≤ e^{(log W)^{7/8}} P(r)` (`ρ ≤ ℓ†`), so the pin RHS (as `Ĵ ≥ 0`). **No premise fails.**
- M2 `3_5:844` cover `|c-a|≤ℓ*∨|c'-b|>ℓ` (R1), `|c'-b|≤ℓ*∨|c-a|>ℓ` (R2), `ℓ*<|c'-b|,|c-a|≤ℓ` (R3): R1∪R2∪R3 = all pairs (terms ≥ 0, overlaps harmless; script: `full/(S1+S2+S3) ≤ 1`).
- M3 `S̃₁`, `(eq:pointwise_loop2)` (`3_5:848`): `𝒜₁={c': |c'-b|>ℓ ∨ ∃c∼c', |c-a|≤ℓ*}`, `(𝓛⁴_alt)^{1/2} ≤ |𝓛²_{(s,-s),(c',b)}| ≤ y²P(|c'-b|)` by `emn2Poly_norm_loop4_alt_le` (`:289`) + `STLWassmExp`: **entry bounds `(GijGEX)` not needed** (T2102a). `P(|c'-b|) ≤ K_n P(r)`: case `|c'-b|>ℓ`: `ρ=ℓ`, `K=1` (`tailW_antitone`); case `|c'-a|≤ℓ*+1`: `ρ' ≥ ρ-(ℓ*+1)`, `r>ℓ†`, row 5.
- M4 `(eq_S1tilde)` `3_5:855`: `stContractPt_holds` (`ContractPt.lean:463`): `Σ_{𝒜₁}Σ_{c∼c'}‖𝓛⁶‖ ≤ 3^d/(W^dη)·M·max‖𝓛³‖`, `M = y²K_nP(r)`.
- M5 3-loop `3_5:857`: `emn2Poly_norm_loop3_le` (`:359`): `‖𝓛³‖ ≤ ‖𝓛²_{(s,-s),(a,a)}‖^{1/2}‖𝓛²_{(σ₂,-σ₂),(b,a)}‖ ≤ y³P(0)^{1/2}P(r)`; `P(0)=Bctl` once `W^{-D} ≤ B_{t,0}` (eventually, `B_{t,0} ≥ (𝔡⁻²+1)⁻¹`). So `W^dS̃₁ ≤ 3^dη⁻¹K_n y⁵ Bctl^{1/2}P(r)²` `(eq:boundwtS_1)`.
- M6 `S̃₂`: `emn2Poly_contractPt_partner` (`:496`) with `𝒜₂={c: |c-a|>ℓ ∨ ∃c'∼c,|c'-b|≤ℓ*}`, same bounds with `a↔b` (so `|c-a| ≥ r-ℓ*-1`).
- M7 `S̃₃` `3_5:871–888` (**ST2-11**).
**Cut.** ST2-10 (`EMn2Exp1`, ns `RBM.Gauss.Sizes`, all public names prefixed `emn2Exp`): `emn2ExpEllStar/EllDag` (ℓ*, ℓ†; `KellStar.lean:54` has ℓ* only inline, no public def), region sums `emn2ExpR1/R2/R3`, cover lemma `emn2Exp_cover` (det.), `emn2Exp_S12_le` (det.: hyp `‖𝓛²_{(s,-s),(x,x')}‖ ≤ y²P(|x-x'|)`, `P(|c'-b|) ≤ KP(r)` on `𝒜₁`/`𝒜₂`; concl. `W^d(Σ_{R1}+Σ_{R2}) ≤ 2·3^dη⁻¹Ky⁵Bctl^{1/2}P(r)²`), `emn2Exp_K_le` (`K_n` eventually `≤ N^{τ/10}`), `emn2Exp_near` (`Prec` of `X·1_{r≤ℓ†}` against the pin RHS), `emn2Exp_far12` (`Prec` of `W^dΣ_{R1∪R2}·1_{r>ℓ†}`). ST2-11: `S̃₃` and assembly. Lead for ST2-11 (numerically checked only): `|𝓛⁶| ≤ ∏_{i=1}^6 (𝓛²_{(s_i,-s_i)}(pair_i))^{1/2}` (`|tr X₁…X₆| ≤ ∏‖X_i‖_{HS}`), no entry bounds.

| quantity | value | constraint | slack |
|---|---|---|---|
| 1 `ε₀'` | `½min(𝔡, dε/2, ε₀)` = `1/40` at `𝔡=ε=1/10, ε₀=1/20, d=3` | `W^{-d}B_{t,0} ≤ W^{-2ε₀'}` ∀ `n` eventually: `W^{-d}(g²+u)⁻¹ ≤ W^{-2𝔡}` (`lam_sq_mul_pow_ge`, `Sizes.lean:193`); `(Nu)⁻¹ ≤ 4N^{-ε} ≤ 4W^{-dε}` (`u ≥ 1-lemT ≥ Im z/(1+‖z‖)`, `ST_one_sub_lemT` `Step2Iterate.lean:1014`, `‖z‖≤3`, `W^d ≤ N`) | `5W^{-m} ≤ W^{-m/2}`, `m=min(2𝔡,dε)`, iff `W^{m/2} ≥ 5` |
| 2 `STPsiClass` | `c_C = min((1+𝔡⁻²)^{-1/2}, (C+1)^{-(d-2)/2})`, `C₁=2`, `C₂=max(2,(d-2)/2)` | window: `W^{-d/2} ≤ c⁻¹Ψ'(0)` (`B_{t,0} ≥ (𝔡⁻²+1)⁻¹`); `r≤C`: `B(ρ) ≥ (ρ+1)^{-(d-2)}B_{t,0}`; ratio: `B(ρ₁)/B(ρ₂) ≤ ((ρ₂+1)/(ρ₁+1))^{d-2} ≤ (r₂/r₁)^{d-2}`; antitone: `BparamR_antitone`; `∀n` clauses via `min` with `W^{-ε₀'}` (ratio of mins ≤ ratio) | constants free of `W,L,λ` (§29); `d≥3` unused |
| 3 `D''` (near case only; far case uses the pin's `D`) | `2+(d-2)/(𝔠d)` = 4 at `d=3, 𝔠=1/6` | `W^{-D''} ≤ B(ρ) ≥ (𝔡⁻²+1)⁻¹(ℓ⁺+1)^{-(d-2)}`, `ℓ ≤ (log W)^{10}L`, `L^d ≤ N ≤ W^{1/𝔠}` (`Bandwidth`, eventually) | `W^{2-o(1)}` (eventually) |
| 4 comparison `Ψ'² ≤ W^{o(1)}P` | `e^{(log W)^{7/8}}` | `ρ/ℓ_t ≤ ℓ†/ℓ_t = (log W)^{7/4}`, any regime; need `2(log W)^{7/8} ≤ (τ/4)log N` eventually | `(log W)^{7/8}/log N → 0` (`W ≤ N`) |
| 5 `K_n` (`P(ρ')/P(ρ)`) | `2^{d-2}exp(2√2(log W)^{5/8})` | needs `ℓ†/2 ≥ ℓ*+1` (⇐ `x^{3/2}(x^{1/4}/2-1) ≥ 1`, `x=log W ≥ 16.94`): then `ρ' ≥ ℓ†/2 ≥ ℓ*+1`, `B(ρ')/B(ρ) ≤ 2^{d-2}`, `√ρ-√ρ' ≤ s/√ρ' ≤ √2(ℓ*+1)/√ℓ†`, `(ℓ*+1) ≤ 2ℓ*` | eventual only (not at `W=32`) |
| 6 loss | `y=N^{τ/10}`, `τ'=τ/5`, `y⁵=N^{τ/2}` | `2·3^d·K_n ≤ N^{τ/2}` (`N→∞`) | closes from `log W ≈ 7.6` (`τ=1`), `32` (`τ=1/2`), `1625` (`τ=1/10`), script `inst.py` |
| 7 `Ĵ` | `≥ 0` | `STJhatM` = sup of norm / `P>0`, so `Bctl^{1/2}+Ĵ³ ≥ Bctl^{1/2}` | — |
| 8 `η` | `η = etaT > 0` | `t ≤ lemT < 1`, `|lemE|<2` (as T2102) | — |

§29 checks: (1) `0 ≤ t ≤ lemT z` only for `η>0`, `u ≥ N^{-1+ε}/4`; (3) no `L^d ≤ W^K` assumed: `L^d ≤ N ≤ W^{1/𝔠}` (eventually) comes from `STFlow` (`Bandwidth`); (4) `Prec` eventual, `STPsiClass` window `∀ᶠ`, all constants (`K_n` aside, which is `N^{o(1)}`) free of `W, L, λ`; the near-case comparison is `D`-independent (`max ≥ first arg`).
Regimes (`ℓ_t = min(max(g/√u,1),L)`): the comparisons `𝒯̃ ≍ W^dΨ²` (row 4), `K_n` (row 5), `W^{-D} ≤ B` use only `B(ρ)=A(ρ+1)^{-(d-2)}+Z`, `Z=(L^du)⁻¹ ≥ 0`, never the sign of `u-g²`, `u-g²/L²`, `u-g²/L^d`. Regime matters only for emptiness of the far set `{r ∈ ℕ: ℓ†<r≤⌊L/2⌋}` (nonempty iff `ℓ†<⌊L/2⌋`): `u ≤ g²/L²` ⇒ `ℓ_t=L`, `exp ≥ e⁻¹` on `r≤L` (`exp_tail_ge`), far set empty (the pin is then the near case alone); `g²/L²<u<g²` ⇒ `ℓ_t=g/√u∈(1,L)`; `u ≥ g²` ⇒ `ℓ_t=1`, far set nonempty iff `(log W)^{7/4}<⌊L/2⌋`; `u ≤ g²/L^d` ⇒ `Z ≥ g⁻² ≥ A(0)`, so `B` is flat up to a factor 2, covered by row 1 via `(Nu)⁻¹`.

### (ii) Concrete instance and checks

Instance of `STEMn2Exp 3`: `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `λ=(2(n+1))^{-6}`), `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z_n=1/2+iN^{-4/5}`, `t≡1/16`, `ε₀=1/20`, `Ψ_n=W^{-1}` (`W^{-3/2} ≤ W^{-1} ≤ W^{-1/20}`), `ℓ_n=ℓ_t=1` (`g/√u<1`; `1 ≤ (log W)^{10}` for `W ≥ e`), `D=4`; `STInitialGT2`, `STLWassmExp` stay hypotheses. `python3 inst.py` (far set nonempty and row 5 first hold at `n=188` (also at the larger `n` listed), `r∈(ℓ†,L/2]`; `n=0` has `ℓ†=9 > L/2=2`):
```
n=0: L=4 logW=3.5 logN=14.6 ell_t=1.00 ell^dag=9 L/2=2 far-window=False ell^dag/2>=ell*+1:False log(2*3^d*K_n)=10.8 (needs tau>=1.49) logPsi0^2=-10.3<=-2eps0'logW=-0.17:True
n=100: L=404 logW=26.5 logN=97.6 ell_t=1.00 ell^dag=310 L/2=202 far-window=False ell^dag/2>=ell*+1:True log(2*3^d*K_n)=26.6 (needs tau>=0.55) logPsi0^2=-79.6<=-2eps0'logW=-1.33:True
n=188: L=756 logW=29.7 logN=108.9 ell_t=1.00 ell^dag=377 L/2=378 far-window=True ell^dag/2>=ell*+1:True log(2*3^d*K_n)=28.2 (needs tau>=0.52) logPsi0^2=-89.0<=-2eps0'logW=-1.48:True
n=1000000: L=4000004 logW=72.5 logN=263.2 ell_t=1.00 ell^dag=1803 L/2=2000002 far-window=True ell^dag/2>=ell*+1:True log(2*3^d*K_n)=45.8 (needs tau>=0.35) logPsi0^2=-217.6<=-2eps0'logW=-3.63:True
first n with far window (ell^dag < L/2) and ell^dag/2 >= ell*+1: n=188
tau=1.0: closes (2*3^d*K_n <= N^(tau/2)) from log W ~ 7.6 (W ~ e^8)
tau=0.5: closes (2*3^d*K_n <= N^(tau/2)) from log W ~ 32.2 (W ~ e^32)
tau=0.1: closes (2*3^d*K_n <= N^(tau/2)) from log W ~ 1624.7 (W ~ e^1625)
```
Comparison `𝒯̃` vs `W^dΨ²` (`python3 prof.py`, `d=3,L=8,W=2,g=1/2,D=4`; all `r ≤ ℓ†`; the ratio lies in `[e^{-(log W)^{7/8}},1]`, and `W^{-D} ≤ B`):
```
d=3 L=8 W=2 g=0.5 D=4.0: g^2=0.25, g^2/L^2=0.00391, g^2/L^d=0.000488; lower bound e^-(logW)^(7/8)=0.4840; W^-D=0.0625
1-t=0.1: ell_t=1.581 ell*=0.912 ell^dag=0.833 B_t0=2.877; ratio Tt/(W^d Psi^2) for r=0..floor(ell^dag):
  ell=0: 1.000  in [lower,1] and W^-D<=B: True
  ell=2: 1.000  in [lower,1] and W^-D<=B: True
  ell=4: 1.000  in [lower,1] and W^-D<=B: True
1-t=0.001: ell_t=8.000 ell*=4.617 ell^dag=4.212 B_t0=5.937; ratio Tt/(W^d Psi^2) for r=0..floor(ell^dag):
  ell=0: 1.000 1.000 1.000 1.000 1.000  in [lower,1] and W^-D<=B: True
  ell=2: 1.000 0.702 0.607 0.607 0.607  in [lower,1] and W^-D<=B: True
  ell=4: 1.000 0.702 0.607 0.542 0.493  in [lower,1] and W^-D<=B: True
1-t=0.0001: ell_t=8.000 ell*=4.617 ell^dag=4.212 B_t0=23.530; ratio Tt/(W^d Psi^2) for r=0..floor(ell^dag):
  ell=0: 1.000 1.000 1.000 1.000 1.000  in [lower,1] and W^-D<=B: True
  ell=2: 1.000 0.702 0.607 0.607 0.607  in [lower,1] and W^-D<=B: True
  ell=4: 1.000 0.702 0.607 0.542 0.493  in [lower,1] and W^-D<=B: True
```
External hypotheses (limit check, lesson 14): one Gaussian sample (`E|X_ij|²=W^{-d}SB`, `H_t=√tX`, `z_t=E+(1-t)m(E)`, `t=1/16`, `L=3`, `ℓ=ℓ_t`, `D=4`), `python3 lim.py`: `max 𝓛²/P` per distance stays bounded as `W` grows (`W=2,3,4`), `‖G-M‖_max` falls, so `STLWassmExp` and `STInitialGT2` hold at the sample up to constants `≤ N^τ` (not a proof of `≺`):
```
lam=0.0156 W=2 N=216 ell=ell_t=1.00: ||G-M||max=0.232 (W^-eps0=0.966); |a-b|=0: max L2/STprof=1.002; |a-b|=1: max L2/STprof=0.000
lam=0.0156 W=3 N=729 ell=ell_t=1.00: ||G-M||max=0.162 (W^-eps0=0.947); |a-b|=0: max L2/STprof=0.980; |a-b|=1: max L2/STprof=0.000
lam=0.0156 W=4 N=1728 ell=ell_t=1.00: ||G-M||max=0.116 (W^-eps0=0.933); |a-b|=0: max L2/STprof=0.968; |a-b|=1: max L2/STprof=0.000
lam=1.0000 W=2 N=216 ell=ell_t=1.03: ||G-M||max=0.109 (W^-eps0=0.966); |a-b|=0: max L2/STprof=1.842; |a-b|=1: max L2/STprof=0.102
lam=1.0000 W=3 N=729 ell=ell_t=1.03: ||G-M||max=0.068 (W^-eps0=0.947); |a-b|=0: max L2/STprof=1.830; |a-b|=1: max L2/STprof=0.089
lam=1.0000 W=4 N=1728 ell=ell_t=1.03: ||G-M||max=0.045 (W^-eps0=0.933); |a-b|=0: max L2/STprof=1.820; |a-b|=1: max L2/STprof=0.085
```
Target check, one sample of `S̃₁` (`python3 s1.py <λ> 1 <ℓ>`; `d=3,L=4,W=2,N=512`, `t=1/16`, `z=1/2+iN^{-4/5}`, literal block sums `S̃_i = W^dΣ^⋆_{R_i}|𝓛⁶|`, bound `η⁻¹Bctl^{1/2}P(r)²`, `|a-b|>ℓ†`, 16128 cases `(σ,a,b)`; shape of `sz0` at `n=0` with `W=2` instead of `32` (`N=2097152` is too large for a dense matrix); a finite-size sanity check, row 5 is not in force):
```
$ python3 s1.py 0.015625 1 2
d=3 L=4 W=2 N=512 lam=0.015625 seed=1 t=0.0625 eta=0.9077 ell=2.0 ell_t=1.000 ell*=0.577 ell^dag=0.527 D=4.0; Bctl^(1/2)=3.6794e-01
y^2 = max|L2_(s,-s)|/STprof = 1.0188
cases (sigma,a,b) with |a-b|>ell^dag: 16128
max S1/bound=2.763e-05  max S2/bound=2.763e-05  max S3/bound=3.920e-13  max full/(S1+S2+S3)=1.000 (<=1 expected)
max [sum_{c' in A1,c~c'} L6]/[3^d/(W^d eta) M L3] = 0.080 (<=1 expected); max K=max_A1 P(|c'-b|)/P(|a-b|) = 5.354; max_A1 sqrt(L4)/(y^2 max(K,1) P(|a-b|)) = 0.356 (<=1 expected)
Holder |L6| <= sqrt(prod_i L2_(s_i,-s_i)(pair_i)) over 400 draws, worst ratio: 0.0857
$ python3 s1.py 1.0 1 2
d=3 L=4 W=2 N=512 lam=1.0 seed=1 t=0.0625 eta=0.9077 ell=2.0 ell_t=1.033 ell*=0.596 ell^dag=0.544 D=4.0; Bctl^(1/2)=2.5807e-01
y^2 = max|L2_(s,-s)|/STprof = 1.9285
cases (sigma,a,b) with |a-b|>ell^dag: 16128
max S1/bound=6.999e-02  max S2/bound=6.999e-02  max S3/bound=2.886e-04  max full/(S1+S2+S3)=1.000 (<=1 expected)
max [sum_{c' in A1,c~c'} L6]/[3^d/(W^d eta) M L3] = 0.084 (<=1 expected); max K=max_A1 P(|c'-b|)/P(|a-b|) = 5.188; max_A1 sqrt(L4)/(y^2 max(K,1) P(|a-b|)) = 0.354 (<=1 expected)
Holder |L6| <= sqrt(prod_i L2_(s_i,-s_i)(pair_i)) over 400 draws, worst ratio: 0.0700
```
All premises hold at the sample (`t ≤ lemT`; `y²` is the smallest constant with `‖𝓛²_{(s,-s)}‖ ≤ y²P`); the cover, contraction chain `≤ 1`, `F1` and the Hölder lead hold; `S̃₁/bound ≤ 0.07`.

### Verdicts
- Target 1 (scales, `Ψ'²≍P` on `r≤ℓ†`, `P(|b-c'|) ≤ K_nP(r)` in both cases): **PASS** (rows 4–5; the second case needs `ℓ†/2 ≥ ℓ*+1`, true eventually, not at small `n`).
- Target 2 (near case from `stEMn2Poly_holds`; the premises `STPsiClass`, `STInitialGT2`, `STLWassm` follow from `STLWassmExp` and `𝒯̃ ≤ B`): **PASS**.
- Target 3 (`S̃₁`, `S̃₂`, contraction, 3-loop): **PASS**; entry bounds `(GijGEX)`/`STGbEXPij` not needed (block Cauchy–Schwarz, F1/F2 of T2102); the `K_n` loss is `N^{o(1)}`. Paper-delta candidates for (d): `T2109a` (`ℓ†/2 ≥ ℓ*+1` is used and holds only for `log W ≥ 16.94`), `T2109b` (truncation `ρ=r∧ℓ⁺` and `min` with `W^{-ε₀'}` for `∀ n` clauses), `T2109c` (no entry bounds).

## (b) Script output — Sun Oct  4 06:21:25 UTC 2026

Branch `t/T2109`, commit `06a008f`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2109`; scratch scripts and outputs in `scratchpad/T2109/`. New file `RBM3D/Induction/EMn2Exp1.lean` (2122 lines); no other file changed (`git diff main...t/T2109 --stat`, b.4).

### b.1 Build and axioms
```
$ lake build RBM3D.Induction.EMn2Exp1 2>&1 | grep -n "EMn2Exp1"   # output of the rebuild after the last edit of the file
332:✔ [3767/3767] Built RBM3D.Induction.EMn2Exp1 (7.5s)
$ lake build RBM3D.Induction.EMn2Exp1 2>&1 | tail -1
Build completed successfully (3767 jobs).
$ lake env lean RBM3D/Induction/EMn2Exp1.lean; echo "exit $?"   # standalone elaboration, all linters on
exit 0
```
```
$ lake env lean axioms.lean | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"
28
$ lake env lean axioms.lean | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]"
'RBM.Gauss.Sizes.emn2ExpSw' depends on axioms: [propext]
```

### b.2 Target statements (extracted from the file by script)
```
$ diff <(sed -n 457,467p RBM3D/Induction/Step2Defs.lean | sed 's/^ *//') <(sed -n '1207,1217p' RBM3D/Induction/EMn2Exp1.lean | sed 's/^ *//'); echo $?   # emn2Exp_near premises vs the pin
0
$ diff <(sed -n 457,467p RBM3D/Induction/Step2Defs.lean | sed 's/^ *//') <(sed -n '1466,1476p' RBM3D/Induction/EMn2Exp1.lean | sed 's/^ *//'); echo $?   # emn2Exp_far12 premises vs the pin
0
$ python3 stmts.py emn2Exp_near emn2Exp_far12 emn2Exp_S12_le emn2Exp_profile_cmp emn2Exp_cover
-- EMn2Exp1.lean:1206
theorem emn2Exp_near (d : ℕ) :
  ... (11 premise lines, identical to `Step2Defs.lean:457-467`) ...
              Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => if (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) ≤
                    emn2ExpEllDag sz n (t n) then
                  ‖STEEk sz n (STflowE z n) (t n) p.1 p.2.1 p.2.2 ω‖ else 0)
                (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2) := by
-- EMn2Exp1.lean:1465
theorem emn2Exp_far12 (d : ℕ) :
  ... (11 premise lines, identical to `Step2Defs.lean:457-467`) ...
              Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => if emn2ExpEllDag sz n (t n) <
                    (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) then
                  emn2ExpS1M sz n (STflowE z n) (t n) (ℓ n) p.1 p.2.1 p.2.2 ω +
                    emn2ExpS2M sz n (STflowE z n) (t n) (ℓ n) p.1 p.2.1 p.2.2 ω else 0)
                (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2) := by
-- EMn2Exp1.lean:699
theorem emn2Exp_S12_le (hH : H.IsHermitian) (hz : 0 < z.im) (σ : Fin 2 → Bool)
    (a b : Zd d L) {y K ℓs ℓ : ℝ} (hy : 0 ≤ y) (hK0 : 0 ≤ K) {Pf : ℕ → ℝ} (hPf : ∀ m, 0 ≤ Pf m)
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Pf (zdistInf d L (x - x')))
    (hK : ∀ m : ℕ, (ℓ < (m : ℝ) ∨ (zdistInf d L (a - b) : ℝ) ≤ (m : ℝ) + ℓs + 1) →
      Pf m ≤ K * Pf (zdistInf d L (a - b))) :
    emn2ExpS1 H z ℓs ℓ σ a b + emn2ExpS2 H z ℓs ℓ σ a b ≤
      2 * 3 ^ d / z.im * K * y ^ 5 * Real.sqrt (Pf 0) * Pf (zdistInf d L (a - b)) ^ 2 := by
-- EMn2Exp1.lean:283
theorem emn2Exp_profile_cmp (n : ℕ) (u D ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hLg1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hs : 2 * (emn2ExpEllStar sz n u + 1) ≤ emn2ExpEllDag sz n u)
    {r m : ℝ} (hr : emn2ExpEllDag sz n u < r)
    (hm : ℓ < m ∨ r ≤ m + emn2ExpEllStar sz n u + 1) :
    emn2ExpPf sz n u D ℓ m ≤ emn2ExpK d ((sz.W n : ℕ) : ℝ) * emn2ExpPf sz n u D ℓ r := by
-- EMn2Exp1.lean:419
theorem emn2Exp_cover (hL : 3 ≤ L) (g ℓs ℓ : ℝ) (σ : Fin 2 → Bool) (a b : Zd d L) :
    ‖(((W : ℕ) : ℂ) ^ d) * ∑ c : Zd d L, ∑ c' : Zd d L, SB d L g c c' *
        loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ ≤
      emn2ExpS1 H z ℓs ℓ σ a b + emn2ExpS2 H z ℓs ℓ σ a b + emn2ExpS3 H z ℓs ℓ σ a b := by
$ grep -nE "^(theorem|def) (emn2Exp_profile_shift|emn2Exp_trunc_cmp|emn2Exp_kellStar_far|emn2Exp_EEk_cover|emn2Exp_EEk_split|emn2Exp_of_far3|emn2ExpS3M|emn2ExpPsi)" RBM3D/Induction/EMn2Exp1.lean | cut -d" " -f1-2
203:theorem emn2Exp_profile_shift;821:def emn2ExpPsi;1390:def emn2ExpS3M;1412:theorem emn2Exp_EEk_cover;1637:theorem emn2Exp_kellStar_far;1652:theorem emn2Exp_trunc_cmp;1685:theorem emn2Exp_EEk_split;1715:theorem emn2Exp_of_far3;
```

### b.3 Compiled nonempty instances (same file, namespace `RBM.Gauss.EMn2Exp1Inst`)
```
$ grep -cE "^example( |$)" RBM3D/Induction/EMn2Exp1.lean   # then per example: line, name and data (docstring heading; script inst_list.py)
19
1851: emn2Exp_cover at the instance matrix: the cut-0 quadratic variation loop is 
1861: emn2Exp_S12_le at the instance matrix: every hypothesis is discharged (the 2
1878: emn2Exp_profile_shift at small numbers (d = 3, L = 4, ilambda = 1/64, t = 1/
1887: The same data, case (2) m ≥ r - s with m ≤ ℓ: r = 3, m = 2 = r - s, ℓ = 2.
1921: emn2Exp_scale_gap at szA: 2 (ℓ* + 1) ≤ ℓ†.
1925: emn2Exp_profile_cmp at szA, case (1): m = 2 > ℓ = 1, r = ℓ† + 1.
1932: emn2Exp_profile_cmp at szA, case (2): m = r - (ℓ* + 1), ℓ = 1.
1954: emn2Exp_trunc_cmp at sz0, n = 0, t = 1/16, D = 1, ℓ = 1, r = 1 ≤ ℓ†
1969: emn2Exp_ev_exp_pow at sz0: eventually exp(2 (log W)^{3/4}) ≤ N^{1/2}.
1986: emn2Exp_psiClass at sz0: the truncated profile at the scale ℓ_n = ℓ_t, D = 1
1993: emn2Exp_EEk_cover and emn2Exp_EEk_split at sz0, n = 0, E = 1/2, t = 1/16,
2000: emn2Exp_EEk_cover and emn2Exp_EEk_split at sz0, n = 0, E = 1/2, t = 1/16,
2025: emn2Exp_near (the near case |a - b| ≤ ℓ†_t of (eq:MG_conclusion3)) at the in
2042: emn2Exp_far12 (S̃₁ + S̃₂ in the far case |a - b| > ℓ†_t) at the same data.
2064: emn2Exp_of_far3 at d = 3: the pin STEMn2Exp 3 follows from the bound of S̃₃ 
2102: emn2Exp_kellStar_far at sz0, 𝔠 = 1/6, Λ = 1, τ = 1/20, δ = 1/200, D = 1,
2112: emn2Exp_one_le_K, emn2Exp_STprof_eq, emn2ExpEllStar_eq at sz0, n = 0: the lo
2114: emn2Exp_one_le_K, emn2Exp_STprof_eq, emn2ExpEllStar_eq at sz0, n = 0: the lo
2118: emn2Exp_one_le_K, emn2Exp_STprof_eq, emn2ExpEllStar_eq at sz0, n = 0: the lo
$ sed -n "2036,2040p" RBM3D/Induction/EMn2Exp1.lean   # application of `emn2Exp_near` (binders of the example: `hI`, `hA`, `D`, `hD`)
  emn2Exp_near 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
    (by norm_num) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) Ψ1_window hI
    (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)) ℓ_range_inst hA D hD
```
Data: `d = 3`; matrix level `L = 3, W = 2`, `H_ij = (i)_0 + (j)_0`, `z = 1/2 + i/4`; scales: small numbers, and `szA` (`W = 2^400`, needed for `(log W)^{1/4} ≥ 4`); model level `sz0`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z0`, `t ≡ 1/16`, `ε₀ = 1/20`, `Ψ = W^{-1}`, `ℓ_n = ℓ_t`, every `D > 0`; `emn2Exp_kellStar_far`: `Λ=1, τ=1/20, δ=1/200, D=1`. Every deterministic hypothesis is discharged; `hI : STInitialGT2`, `hA : STLWassmExp` (all `D`) and, for `emn2Exp_of_far3`, `h3` stay hypotheses (other gates' pins).

### b.4 Name clashes, hygiene, scope
```
$ grep -rn "emn2Exp" RBM3D RBM3D.lean docs/tickets /Users/junyin/Lean_proof/RBM1D/RBM1D /Users/junyin/Lean_proof/RBM2D/RBM2D | grep -v "^RBM3D/Induction/EMn2Exp1.lean" | wc -l
       0
$ grep -nE "^(theorem|def) " RBM3D/Induction/EMn2Exp1.lean | wc -l   # public declarations (the other 44 top-level declarations are private)
      29
$ grep -nEw "sorry|admit|axiom|native_decide|sorryAx" RBM3D/Induction/EMn2Exp1.lean | wc -l
       0
$ git diff main...t/T2109 --stat | tail -2
 RBM3D/Induction/EMn2Exp1.lean | 2122 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2122 insertions(+)
$ git status --short RBM3D/Test/Axioms.lean RBM3D.lean | wc -l   # registry file and root untouched
       0
```

### b.5 Ports and registry
Nothing was ported from RBM1D/RBM2D (their sources were only searched by `grep` in the name-clash check above; no `git -C ../RBM2D` command was run, no diff-stat to report). Copies of private lemmas of the merged `RBM3D/Induction/EMn2Poly.lean` (commit `90a2761`): `zdistInf_{zero_eq,neg_eq,add_le_add,tri,sub_comm}` (l. 438-461), `norm_SB_le_one`, `SB_eq_zero_of_far` (l. 466, 474), `stochDomAt_of_subset'` (l. 797), `STEEkM_{zero,one}_eq` (l. 810, 821); `loop3_ctrl`, `part1_le`, `part2_le`, `emn2_ee_le` (l. 514, 534, 615, 679) are adapted (profile `Pf` and the regions of `(eq;S123)` in place of `Ψ` and `R₁/R₂`).
```
$ lake build 2>&1 | tail -1   # baseline: the root does not import the module; exit 0
Build completed successfully (3855 jobs).
$ lake env lean precheck_base.lean   # `import RBM3D` + `#assert_rbm_axioms` (root without the module); exit 0
1:axiom audit: 3349 theorems, 1206 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
114:premises found by scanning: 82 (borrowed 2, owed 64, structural 16).
115:registry: 5 borrowed + 102 owed + 39 structural; 64 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
$ lake env lean precheck.lean        # `import RBM3D`, `import RBM3D.Induction.EMn2Exp1`, `#assert_rbm_axioms`; exit 0
1:axiom audit: 3368 theorems, 1219 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
114:premises found by scanning: 82 (borrowed 2, owed 64, structural 16).
115:registry: 5 borrowed + 102 owed + 39 structural; 64 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
$ diff precheck_base.out precheck.out
1c1
< axiom audit: 3349 theorems, 1206 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 3368 theorems, 1219 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
72c72
<   RBM.Gauss.Sizes.STInitialGT2: 4 [no certificate]
---
>   RBM.Gauss.Sizes.STInitialGT2: 7 [no certificate]
74c74
<   RBM.Gauss.Sizes.STLWassmExp: 2 [no certificate]
---
>   RBM.Gauss.Sizes.STLWassmExp: 5 [no certificate]
$ lake build 2>&1 | tail -1   # `import RBM3D.Induction.EMn2Exp1` temporarily added to RBM3D.lean after the last import; exit 0
Build completed successfully (3856 jobs).
583:info: RBM3D.lean:155:0: axiom audit: 3368 theorems, 1219 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ git status --short | wc -l   # RBM3D.lean restored, file committed
       0
```

### b.6 Numeric sanity of the real-analysis steps (finite samples, not proofs)
```
$ python3 shift_check.py   # abstract shift lemma (`d ∈ {3,4,5,6}`, natural `d-2` = real `d-2`), 300000 random cases
cases 300000 max P(m)/(K0*P(r)) = 0.482604508498435 (<= 1 expected) at (d,L,g,t,ell,W,D,s,ld,r,m) = (3, 97, 0.0017, 0.5617, 67.5, 39.93, 7.62, 0.0, 47.44, 131.93, 133.47)
$ python3 comp_check.py    # truncated profile vs `W^{-d} 𝒯̃`
P <= Psi'^2 (every r): 300000 cases, max P/Psi'^2 = 0.9999999999999986 (<= 1 expected)
Psi'^2 <= 2 exp((log W)^{7/8}) P (r <= l_dag): 222800 cases, max ratio = 0.49999742342889203 (<= 1 expected)
```

### b.7 Narrative
1. File `EMn2Exp1.lean` (ns `RBM.Gauss.Sizes`), imports `EMn2Poly`, `Step2Iterate` (`ST_Bdata_holds`, `ST_prof_le_Bctl`, `ST_prec_*`) and `KellStar`; 29 public and 44 private declarations, 19 `example`s; `Test/Axioms.lean`, `RBM3D.lean` untouched.
2. Target 1 (§1-2, §9): `emn2ExpEllStar` is the inline scale of `KellStarEv` (`emn2ExpEllStar_eq := rfl`; `emn2Exp_kellStar_far` restates `kellStarEv` with it), `emn2ExpEllDag`, `emn2ExpPf` (`STprof` at `|a-b|`); `emn2Exp_profile_shift`/`_cmp`: `P(m) ≤ K_n P(r)` for `r > ℓ†` and `m > ℓ` or `m ≥ r-ℓ*-1` (`3_5:851-853`), `K_n = 2^{d-2}exp(2(log W)^{3/4})`, under `2(ℓ*+1) ≤ ℓ†` (`emn2Exp_scale_gap`: `(log W)^{1/4} ≥ 4`); `emn2Exp_trunc_cmp`: `Ψ² ≍ W^{-d}𝒯̃` for `r ≤ ℓ†`.
3. Target 2 (§6): `emn2Exp_near` applies `stEMn2Poly_holds` to `emn2ExpPsi`. **No premise of `STEMn2Poly` fails**: `STPsiClass` (private `emn2Exp_psiClass`, `C₁ = 2`, `C₂ = d+2`), `STLWassm` from `STLWassmExp` at the same `D`, `STInitialGT2` from `STInitialGT2.1` (`ε' ≤ ε₀`) and `STLWassmExp` with `ST_prec_sup`; `Ψ'(r)² ≤ 2exp((log W)^{7/8})W^{-d}𝒯̃(r)` for `r ≤ ℓ†`.
4. Target 3 (§3-4, §7-8): `emn2ExpS1/S2/S3` (sums over `|c-c'| ≤ 1` on the three regions), cover `emn2Exp_cover` (`|S^{(B)}| ≤ 1`, support `|c-c'| ≤ 1`); `emn2Exp_S12_le`: `stContractPt_holds` with `𝒜₁` and the partner with `𝒜₂`, `M = y²K P(r)`, 3-loop `≤ y√P(0)·y²P(r)` (`emn2Poly_norm_loop3_le`, `emn2Poly_norm_loop4_alt_le`): **no `(GijGEX)`**; `emn2Exp_far12`: good event of `STLWassmExp` at `τ/5`, `P(0) ≤ (1+cB⁻¹)Bctl`, `2·3^dK_n√(1+cB⁻¹) ≤ N^{τ/2}` eventually (`emn2Exp_ev_exp_pow`).
5. For ST2-11: `emn2Exp_EEk_split` (both cuts via `emn2ExpSw`) and `emn2Exp_of_far3` (body of `STEMn2Exp` from `h3 : Prec (S̃₃ 1_far) ≺ η⁻¹[Bctl^{1/2}+Ĵ³]P²`); the near and far12 statements are diff-identical to the pin's premises (b.2).
6. Premises used: near: `STFlow`, `0 ≤ t ≤ lemT`, `ε₀`, `STInitialGT2.1`, `ℓ ≥ 0`, `STLWassmExp`; far12: `STFlow`, `0 ≤ t ≤ lemT`, `ℓ ≥ 0`, `STLWassmExp` at `D`. DECISIONS §29: (1) `0 ≤ t ≤ lemT` only for `η > 0`, `t < 1` (`Bctl > 0`) and `ST_Bdata_holds`; (2) no regime of `ℓ_t` (only `1 ≤ ℓ_t`); (3) no `L^d ≤ W^K`; (4) eventual `∀ᶠ`, constants `3^d`, `2^{d-2}`, `cB(𝔡)` free of `W, L, λ`.
7. Section (a) needs no (a′): no mistake found. Lean differs from its proof map in `Ψ'` (`+W^{-D}`, no `D''`), in `K_n` and in `P(0) ≤ (1+cB⁻¹)Bctl` (T2109b, T2109e; verdicts unchanged).

## (c) Verified Mathlib names (all used by the compiled module; `#check` of 106 identifiers, script `names.lean`, no unknown identifier)
- `Real.sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2`; `Real.sqrt_le_sqrt`, `Real.sqrt_mul (0 ≤ x) y`, `Real.sqrt_sq`, `Real.sq_sqrt`, `Real.sqrt_eq_rpow : √x = x ^ (1/2)`, `Real.sqrt_pos`, `Real.sqrt_nonneg`, `Real.sqrt_one`
- `Real.rpow_def_of_pos (0 < x) y : x ^ y = exp (log x * y)`; `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_natCast`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.rpow_le_rpow`; `Real.rpow_le_rpow_of_exponent_le : 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z`; `Real.one_le_rpow : 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z`; `Real.rpow_le_one_of_one_le_of_nonpos : 1 ≤ x → z ≤ 0 → x ^ z ≤ 1`
- `Real.pow_rpow_inv_natCast : 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x`; `Real.log_two_gt_d9 : 0.6931471803 < Real.log 2`; `Real.log_pow`, `Real.log_nonneg`, `Real.log_le_log`, `Real.exp_log : 0 < x → exp (log x) = x`, `Real.exp_nat_mul : exp (↑n * x) = exp x ^ n`, `Real.one_le_exp`, `Real.exp_le_exp`, `Real.exp_add`, `Real.exp_pos`, `Real.exp_le_one_iff`
- `Real.tendsto_log_atTop`, `tendsto_rpow_atTop : 0 < y → Tendsto (fun x => x ^ y) atTop atTop`, `tendsto_natCast_atTop_iff`, `tendsto_id.const_mul_atTop`, `Filter.Tendsto.eventually_ge_atTop`, `eventually_gt_atTop`
- `one_le_pow₀ : 1 ≤ a → 1 ≤ a ^ n`; `pow_le_pow_left₀ : 0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n`; `le_self_pow₀ : 1 ≤ a → n ≠ 0 → a ≤ a ^ n`; `le_of_sq_le_sq : a ^ 2 ≤ b ^ 2 → 0 ≤ b → a ≤ b`; `div_le_iff₀`; `le_mul_of_one_le_left : 0 ≤ b → 1 ≤ a → b ≤ a * b`; `one_le_mul_of_one_le_of_one_le`; `inv_le_one_of_one_le₀`
- `Finset.sum_subset : s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑ s₁ f = ∑ s₂ f`; `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.sum_filter`, `Finset.sum_comm`, `Finset.sum_add_distrib`, `Finset.single_le_sum`, `Finset.sup_le`, `Finset.sup_congr`; `Nat.pow_le_pow_left : n ≤ m → ∀ i, n ^ i ≤ m ^ i`; `Complex.norm_natCast`; `star_natCast`
- RBM3D: `ST_Bdata_holds`, `ST_prof_le_Bctl`, `ST_prec_mono_eventually`, `ST_prec_sup`, `ST_W_tendsto`, `ST_Wpow_le_size`, `ST_size_rpow_neg_le`, `ST_size_pow_small`, `ST_rpow_neg_half`, `ST_rpow_sq`, `ST_flow_im_pos`, `ST_JhatM_nonneg`, `ST_STprof_pos`, `STBctl_pos`, `kellStarEv`, `StochDomAt.{of_subset,add,trans,refl,const_mul_left,of_le_left,precomp_param}`, `tailT_antitone`, `tailW_pos`, `BparamR_natCast`, `one_le_ellT`, `norm_loopM_le`
- Absent: `Real.sqrt_add_le` (subadditivity of `Real.sqrt`; `grep -rn sqrt_add_le Mathlib | wc -l` = 0), proved locally as `emn2Exp_sqrt_add_le`. Deprecated (compile warning, replaced): `if_true`, `if_false` (use `ite_true`, `ite_false`).

## (d) Open issues and paper-delta candidates
1. **Remaining for ST2-11:** `S̃₃` on the far pairs = the hypothesis `h3` of `emn2Exp_of_far3` (`emn2ExpS3M`: `ℓ* < |c'-b| ≤ ℓ`, `ℓ* < |c-a| ≤ ℓ`; `ζ = η⁻¹[Bctl^{1/2}+Ĵ³]P²`, the pin's premises). `emn2Exp_EEk_split` gives the pointwise split; `emn2Exp_kellStar_far` gives the far field of `Θ`, `Θ_s^{-1}Θ_u` beyond `δℓ*`.
2. **T2109a** (`3_5:851-852`): `|b-c'| ≥ |a-b|-(ℓ*+1) = (1-o(1))|a-b|` is used as `2(ℓ*+1) ≤ ℓ†` (hypothesis of `emn2Exp_profile_cmp`; `emn2Exp_scale_gap` under `(log W)^{1/4} ≥ 4`, eventually); (a) row 5: not at small `n`.
3. **T2109b** (`3_5:833-838`): the truncated `Ψ_t(r) = (W^{-d}B_{t,r∧ℓ})^{1/2}` is replaced by `Ψ'_n(r) = min(√(W^{-d}(B_{t,r∧ℓ⁺}+W^{-D})), W^{-ε'})`: the cap makes clause 1 of `STPsiClass` (`Ψ ≤ W^{-ε'}`, every `n`) true and clauses 2, 4 survive it, `ℓ⁺ = max(ℓ,0)`, the `+W^{-D}` gives `W^{-d}𝒯̃ ≤ Ψ'²` for every `r` and `D` (the paper's second fact needs `W^{-D} ≲ B_{t,r∧ℓ}`: `emn2Exp_trunc_cmp` (ii)); no `D''`.
4. **T2109c** (`3_5:848-858`, cf. T2102a): `(eq:pointwise_loop2)` and the 3-loop bound follow from `(eq:LW_assm_exp)` by block Cauchy-Schwarz; `(GijGEX)`, `(GiiGEX)` do not occur.
5. **T2109d** (`3_5:842-845`): `R₃` is read as `ℓ* < |c'-b| ≤ ℓ` and `ℓ* < |c-a| ≤ ℓ`, the complement of `R₁ ∪ R₂`; the cover has constant `1` (`|S^{(B)}| ≤ 1`).
6. **T2109e** (losses): `K_n`, `√(1+cB⁻¹)` (`P(0) ≤ (1+cB⁻¹)W^{-d}B_{t,0}`, `cB` depends on `𝔡` only) and `4√(1+cB⁻¹)exp(2(log W)^{7/8})` (near case) are `N^{o(1)}`, absorbed in `≺` (`emn2Exp_ev_exp_pow`).
7. **T2109f**: premises kept (diff-identical to the pin) but unused: both theorems `Ψ`, its window, `STInitialGT2.2`, `ℓ ≤ (log W)^{10}ℓ_t`; far12 also `ε₀`, `STInitialGT2.1`. `STEMn2Exp` unchanged.
8. **Registry** (DECISIONS §20): `Test/Axioms.lean` untouched; pre-check exit 0, 82 premises found (same as baseline); `STEMn2Exp` stays owed: `emn2Exp_of_far3` is stated with the unfolded body (a theorem with head `STEMn2Exp` would be counted as a proof by `scanPremises`; §20 allows lines in three tables, `RBM.Audit.certificates` is a fourth), and `emn2Exp_psiClass` is `private` by the same rule of `scanPremises` (a public theorem with head `STPsiClass` would be counted as a proof of that premise).
9. Lean's `d - 2` is natural subtraction (`B_{t,r}`); for `d ≤ 2` the profile is flat and all lemmas hold with exponent `0`; the numeric scripts use `d ≥ 3`. (a) reports the far window `ℓ† < r ≤ ⌊L/2⌋` first nonempty at `n = 188` for `sz0`: the instances are asymptotic, the near case is nonempty for all `n`.
