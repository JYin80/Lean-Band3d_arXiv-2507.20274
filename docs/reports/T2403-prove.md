Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 02:26:57 UTC 2026

Notation: `|·| = zdistD` (ℓ¹ torus distance); `c₀ = BAct_rate d Λ κ = min(log(1+κ/(4dΛ)), κ/2)` (`CombesThomas.lean:45`); `μ = BAp5s_rate`; `c = c_λ = GreenStab_clam = min(c₀/12, μ/6)` (`GreenStab.lean:221`); `Λ = 𝔡⁻¹`; `S = expC(d−2, c₀/2)`, `S₄ = expC(d−2, c₀/4)`, `ρ = c₀⁻¹ expC(d−2, c₀)`, `ρ̂ = c₀⁻¹S`, `C_Θ̂ = GreenStab_CTheta`; `P = Φ_N` (the LDE factor of `LDERow/LDECol/LDEQuad`); `δ = W^{-ε₀}`; `𝔗_c(a,a') = Σ_{α,β} φ(α,β) e^{-c(|α−a|+|β−a'|)} + Ψ e^{-c|a−a'|}`.

**Target 1 in mathematics** (deterministic, abstract form; the only form with a nonempty instance at `t > 0`, see Verdict). Data: `L ≥ 3`, `Vtx = Zd × Fin(W^d)`, `M_{uv} = 1_{o(u)=o(v)} Mb_{[u][v]}`, `|Mb_ab| ≤ c₀⁻¹e^{-c₀|a−b|}`, `max_a Σ_b e^{-(c₀/2)|a−b|} ≤ S`, `max_c Σ_b |Mb_bc| ≤ ρ`, `0 ≤ t ≤ 1`, `κ ≤ |m| ≤ 1`, `g₀ ∈ [0, Λ]`, `P ≥ 1`, `δ ≤ κ/2`, `W^{-d} ≤ δ²`, `φ ≥ 0`, `Ψ ≥ W^{-d/2}`, `Ψ > 0`, `0 < φ`, `0 < c ≤ min(c₀/12, 1)`; arrays `Δ, 𝒜'_w, 𝔛_{uy}` with `|Δ| ≤ δ`; `v̄_a = W^{-d}Σ_{k∈a}Δ_kk`; (E3′) `Δ_xy = Σ_{b'} Mb_{ab'}[t v̄_{b'}M_{wy} + (t v̄_{b'} − 𝒜'_w)Δ_wy − 𝒜'_w M_wy − 𝔛_wy]`, `w = (b', o_x)`; `Θ(1 − tM^{(+,+)}) = 1` and `sup_b Σ_{a'}|Θ_{ba'}|e^{2c|b−a'|} ≤ C_Θ̂`; pointwise (X\*) and (Ξ) in the merged forms (`GreenCore.lean:1066, 1130`, kernel `T = GreenCore_T`); (C2). Conclusion: `|Δ_xy| ≤ 2 C_ℓ' P 𝔗_c([x],[y])` for all `x, y` (diagonal included).
**D3.4 → merged names:** `L1 = −ΣM𝒜'M` ← `GreenCore_Xi`; `L2 = −ΣM𝔛` ← `GreenCore_Xstar`; `Δ = L1+L2+L3+Q` ← `GreenCore_E3`, `GreenCore_K` (`𝒦 = (t v̄ − 𝒜')Δ − 𝒜'M − 𝔛`); kernel preservation `Σ_{b'}|M_{ab'}|𝔗_c(b',·) ≤ ρ̂ 𝔗_c(a,·)` ← the hypotheses `hdec`, `hS` (the merged `baM_rhohat` is the same bound); `v̄ = Θ u` ← `BATheta_resolvent` (`Θ = 1 + tM^{(+,+)}Θ = 1 + tΘM^{(+,+)}`, `0 ≤ t < 1`); `Θ` weight ← `baTheta_weighted_l1`.
**Chain used (checked by hand, constants in the script):** (a) `𝔗_c(a'',c'') ≤ e^{c(|a−a''|+|c'−c''|)} 𝔗_c(a,c')`; (b) `Σ_{b'}|M_{ab'}|e^{c|a−b'|} ≤ ρ̂` for `c ≤ c₀/2`; (c) `T ≤ C_T 𝔗_c` for `c ≤ c₀/4`; (d) `|v̄_{b'}| ≤ C_Θ̂ sup_{a''}(|u_{a''}|/𝔗_c(a'',a''))·𝔗_c(b',b')` from (a) with `a''→b'` (so only the weighted `ℓ¹` bound of `Θ` is used, not its pointwise decay); (e) `L3 ≤ c₀⁻¹ρ̂ C_Θ̂ (…)𝔗_c(a,c)`. This gives `𝒩 ≤ C_ℓ'P + θ₀(1+ρ̂C_Θ̂/c₀)𝒩` with the constants below.

### (i) Exponent table
| quantity | value (κ=0.044 / κ=0.5; Λ=10, d=3) | constraint | slack |
|---|---|---|---|
| `c₀` | 3.67e-4 / 4.16e-3 | `> 0`; `hdec` (merged `BAMB_decay_large`) | none needed |
| `μ` | 1.5e-50 / 1.3e-32 | `μ ≤ c₀` (min in def) | `c₀/μ = 2.5e46 / 3.2e29` |
| `c = c_λ` | 2.5e-51 / 2.1e-33; `(d,κ,Λ)` only, not `ε`, `L`, `n` | `c ≤ c₀/4` (T≤C_T𝔗), `c ≤ c₀/2` (ρ̂ bound), `c ≤ 1`, `c ≤ μ/6` (weight `2c ≤ μ/3` of `baTheta_weighted_l1`) | `c₀/4c ≥ 3`, `c₀/2c ≥ 6`, `μ/6` tight |
| `S, ρ, ρ̂` | 5.4e18, 9.3e20, 1.5e22 / 3.3e14, 4.9e15, 7.9e16 | uniform in `L, W`; `ρ̂ ≥ 1` (so `1+ρ̂C_Θ̂/c₀ ≤ 1+ρ̂²C_Θ̂/c₀`: the (a′) shape of (C2) implies this one) | — |
| `C_Θ̂ = C₅(1+Λ²S_{2μ/3})` | 3.3e253 / 5.9e162 | `≥ sup_b Σ_{a'}|Θ_{ba'}|e^{2c|b−a'|}` | enters (C2) only |
| `C_T` | `max(2c₀⁻¹√S, √(16ρPc₀⁻¹S))` | `T ≤ C_T 𝔗_c` | — |
| `e_X, e'` | `√(2P)√13 κ⁻¹δ`, `2dg₀e^c e_X` | coefficient of `|Δ|` in (X\*), of `Σ_l|D_lw||Δ_wl|` in (Ξ) (Lean forms; (a′) D3.3 has `3κ⁻¹a`, T2390l) | — |
| `s_X, s_A` | `s_X = √(2P)(1+2/(κc₀))C_T`; `s_A = [√13κ⁻¹δ(1+√(2P)) + √(2P)(1+2/(κc₀))e^{c₀/4}2dg₀]C_T + √(2P)+√P` | sources; both `≤ const·P` (`δ ≤ κ/2`, `P ≥ 1`) | — |
| `η_tot` | `e'/c₀ + e_X + η₁`; `η₁ = δ + [..]T₀ + √(2P)φ_max + √(PW^{-d}) + 2dg₀e_Xδ`; `T₀ = 2c₀⁻¹√S W^{-d/2} + √(16ρPc₀⁻¹S) S₄ φ_max` | bound of `sup|tv̄−𝒜'|` plus `Δ`-linear coefficients | `∝ P^{3/2}` (`φ_max = P^{1/2}δ`) |
| (C1) | `8ρρ̂θ ≤ 1`, `θ = GreenCore_theta` | `θ ∝ Pδ²` | threshold `log₁₀δ*` below |
| (C2) | `ρ̂ η_tot (1 + ρ̂C_Θ̂/c₀) ≤ ½`; `C_ℓ'P = ρ̂(s_A/c₀ + s_X)(1+ρ̂C_Θ̂/c₀)` | absorption `𝒩 ≤ C_ℓ'P + ½𝒩` | below |
| `K_BA` | `ρ(1+16κ⁻⁴)` = 4.0e27 / 1.3e18 | `K_BAδ ≤ ½` is **not used** by D3.4 (only (C1), (C2)); `BAStab` is not used either | log₁₀δ\*: −27.9 / −18.4 |
| `𝔠` | `W ≥ N^𝔠` (`BAFlow.Admissible`) | `τ₀ < …` rows below | `flow_sz0`: `𝔠 = 1/6` |
| `ε₀` | any `> 0` | window `[W^{-d/2}, W^{-ε₀}]` nonempty ⇒ `W^{-d/2} ≤ W^{-ε₀}` ⇒ `W^{-d} ≤ δ²` (no separate `ε₀ ≤ d/2`) | `flow_sz0` row: `ε₀ = 1/10` |
| `τ₀` | `min(τ/2, 𝔠ε₀/2)`; `P = N^{τ₀}`, `φ = N^{τ₀/2}Φ_n` | (C1): `τ₀ < 2𝔠ε₀`; (C2): `3τ₀/2 < 𝔠ε₀`; absorption of `N^{3τ₀/2}` into `N^τ`: `3τ₀/2 < τ` | `𝔠ε₀ = 1/60`: 1/40, 1/240, ≥ τ/4 (rows below) |
| `W^{-D}` | not used | | |
Probability layer: failure events `¬LDERow, ¬LDECol` (pairs `≤ N²`), `¬LDEQuad, ¬diag` (`N` sites), `¬premise` (union already inside `StochDomAt`); each `≤ N^{-(D'+5)}` (merged `PerTimeDomAt`, `HighProbAt.biInter/inter`, `StochDomAt.highProb`); `Ω` is the indicator `indMax` (no probability). Nothing is owed to G6a: the loop premise is a hypothesis of the pin, `baLDEin_holds` is unconditional, no fluctuation averaging.
Command and output (analytic constants at uniform κ, G2; worst case `g₀ = Λ`; exponent rows at `flow_sz0`):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2403/tableA.py
d=3, Lambda=1/frak_d=10, worst case g0=Lambda; P=Phi_N=N^tau0, phi_max=P^(1/2) delta, W^{-d/2}<=delta
kappa=0.044
  c0=1e-3.44  mu=1e-49.83  cl=1e-50.61  S=1e18.74  rho=1e20.97  rhoh=1e22.17  C5=1e47.71  CTh=1e253.51
  log10 delta*: (C1)=-26.8  (C2)=-350.7  (K_BA<=1/2, not used by D3.4)=-27.9 ; K_BA=3.96e+27
  P-scaling at P=1e3: theta0(P)/(P^1.5 theta0(1)) = 1.0000 ; theta(P)/(P theta(1)) = 0.0010 (both <= 1)
kappa=0.5
  c0=1e-2.38  mu=1e-31.89  cl=1e-32.67  S=1e14.52  rho=1e15.69  rhoh=1e16.90  C5=1e28.71  CTh=1e162.77
  log10 delta*: (C1)=-19.6  (C2)=-236.8  (K_BA<=1/2, not used by D3.4)=-18.4 ; K_BA=1.27e+18
  P-scaling at P=1e3: theta0(P)/(P^1.5 theta0(1)) = 0.9999 ; theta(P)/(P theta(1)) = 0.0012 (both <= 1)
tau=1/100 tau0=1/200 | (C1) 2c*eps0-tau0=17/600 | (C2) c*eps0-3tau0/2=11/1200 | absorb tau-3tau0/2=1/400
tau=1/10 tau0=1/120 | (C1) 2c*eps0-tau0=1/40 | (C2) c*eps0-3tau0/2=1/240 | absorb tau-3tau0/2=7/80
tau=1 tau0=1/120 | (C1) 2c*eps0-tau0=1/40 | (C2) c*eps0-3tau0/2=1/240 | absorb tau-3tau0/2=79/80
flow_sz0 (kappa=1/2): (C2) needs N^{margin} >= 10^236.8 -> log10 N >= 56827 at margin 0.00417 (eventual in n, finite, independent of n)
```
Reading: (C1), (C2) are eventual in `n` for each fixed `(κ, 𝔡, ε₀)` with a finite, `n`-independent threshold (`τ₀`-slack ≥ 𝔠ε₀/4 in (C2)); (C2) is dominated by `C_Θ̂`, i.e. by the tiny `μ`. These thresholds are not witnesses; the instance below uses the data's own constants.

### (ii) One concrete nondegenerate instance
Target 1 at `d = 3`, `L = 4` (64 blocks), `t = 1/2`, `Λ = 10`, `κ = 1/2` (the `flow_sz0` value), real `BAReal` datum `g₀ = 0.013, E = 0` with `m` solving (self_m); `W = 32768`, `ε₀ = 1.4`, `N = (WL)^d`; `Δ_xy = δ(1_{x=y} + ½·1_{x≠y, o(x)=o(y)}) ≠ 0` (D4 of T2390 (a′)), `𝒜'_w = α ≠ 0`, `𝔛` and `𝒦 = M⁻¹Δ − 𝒮[Δ]M` defined so that (E3′) holds; `c₀, S, ρ, C_Θ̂` are the data's own constants (hypotheses, verified numerically). Offset-sector reduction (only `W^{-d}` enters).
```
$ cd .../scratchpad/T2403 && python3 inst.py
BAReal datum: g0=0.013 E=0.0 m=0.000000+0.999494i |m|=0.9995 Im m=0.9995 residual=2.2e-16 kappa(used)=0.500 <= Im m: True
c0=1.000  hdec holds: True   S=sum e^{-(c0/2)|.|} = 17.192   rho=max col l1 |M| = 1.0827   rhohat=S/c0=17.192
t=0.50  Theta=(1-tM^{++})^{-1}: sup_b sum_a' |Theta_ba'| e^{2c|b-a'|} = 0.6672 (c=c0/12=0.08333)   ||Theta||_{inf->inf}=0.6671
W=32768 N=(WL)^d=2.252e+15 eps0=1.40 delta=W^-eps0=4.768e-07  window [W^{-3/2}, W^{-eps0}] = [1.686e-07, 4.768e-07] ∋ Psi=3.372e-07: True  W^{-d}=2.84e-14 <= delta^2=2.27e-13: True  delta<=kappa/2: True
(C1) 8 rho rhohat theta = 6.225e-09 <= 1: True
(E3') residual max|Delta - RHS| = 4.24e-22  (max|Delta| = 4.77e-07)  Delta != 0: True, X != 0: True (max|X|=6.31e-07), A' = alpha = 8.43e-08 != 0
(X*) max |X_wy| / bound = 3.404e-04  holds: True
(Xi) |A'_w| = 8.429e-08 <= bound min = 1.864e-04 : True
closure: eta_tot = 1.922e-04   theta0 = rhohat*eta_tot = 3.304e-03   (C2) theta0*(1+rhohat*C_Th/c0) = 4.125e-02 <= 1/2: True
         C_l' P = 2.933e+04   claimed bound 2 C_l' P = 5.867e+04   actual N = max|Delta_xy|/T_c(a,c) = 3.982e-04   |Delta_xy| <= 2C_l'P T_c: True  (margin 1.5e+08)
K_BA delta (analytic K_Theta=16/kappa^4) = 1.327e-04   K_BA delta (data K_Theta=||Theta||) = 8.607e-07 <= 1/2: True  (not used by D3.4)
N = (W L)^d = 2.252e+15 ; c_lam rate used c = 0.08333 <= c0/12: True, <= c0/4 (T <= C_T T_c): True
```
Here `P = 1`, `φ ≡ δ`, `Ψ = 2W^{-3/2}`, `g₀ ≤ Λ`. A carrier-form instance (actual `G`, `X`) at `t = 1/2` does not exist in Lean: `Δ = −MYG` contains the term `t m` of size `O(t)` unless `X` is a full random sample (T2390 R2); hence the abstract form above.
Targets 2, 3 (data of the compiled example, `GreenCore.lean:1659`): `flow_sz0` (`κ = 1/2, ε = 1/10, 𝔠 = 1/6, 𝔡 = 1/10`), `t ≡ 1/2 ≤ T₀`, `ε₀ = 1/10`, `Φ_n = W^{-1/10}`, `Ψ_n = W^{-1}`: window `W^{-3/2} ≤ W^{-1} ≤ W^{-1/10}` and `Φ_n ≤ W^{-ε₀}` hold; `W ≥ N^{1/6}` (`sz0_bandwidth`). Target 2 at this datum: `BAStab … (16κ⁻⁴) = 256`, `0 ≤ t ≤ 1`, `BAReal` from `BAflow_real`; the instance of `baStab_of_real` is already in `GreenStab.lean` (`inst_baStab`).
External hypothesis of the pin (the loop premise `1_Ω‖𝓛^{(2)}‖ ≺ Φ_n²`, supplied by the consumer, implied by `STLmaxgL` k = 2, `‖𝓛^{(2)}‖ ≺ Bctl = W^{-d}Bparam(d,L,λ,t,0)`): limit computation at `t = 1/2`, `Φ_n = W^{-1/10}`:
```
$ python3 prem.py   (Bparam = (lam^2+|1-t|)^-1 + (L^d |1-t|)^-1 ; sz0: L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6)
n=0      L=4      W=3.200e+01 lam=1.56e-02 Bparam=2.0303  Bctl/Phi^2 = 1.239e-04 (<=3 W^-2.8 = 1.831e-04)
n=1      L=8      W=1.024e+03 lam=2.44e-04 Bparam=2.0039  Bctl/Phi^2 = 7.465e-09 (<=3 W^-2.8 = 1.118e-08)
n=100    L=404    W=3.363e+11 lam=1.47e-14 Bparam=2.0000  Bctl/Phi^2 = 1.062e-32 (<=3 W^-2.8 = 1.593e-32)
n=10000  L=40004  W=3.202e+21 lam=1.56e-26 Bparam=2.0000  Bctl/Phi^2 = 1.219e-60 (<=3 W^-2.8 = 1.828e-60)
```
Limit `Bctl/Φ_n² = Bparam·W^{-2.8} → 0` (`Bparam → 2`): the premise is consistent with the carried induction pin at the same data.

## Verdicts
- **Target 1 (D3.4 closure): PASS** in the abstract form above. (C1), (C2) close eventually with the exponents `τ₀ = min(τ/2, 𝔠ε₀/2)`; the instance has every hypothesis at once (finite `L`, true constants). The merged (X\*), (Ξ) have the coefficients of the table, not those of (a′) D3.3; (C2) keeps the shape `η(ρ̂+ρ̂²c₀⁻¹C_Θ̂) ≤ ½`.
- **Target 2 (`BAStab … (16κ⁻⁴)`): PASS** (body of `baStab_of_real`, `0 ≤ t ≤ 1`, `BAReal`).
- **Target 3 (`baGbEXPij'_holds : BAGbEXPij' d`): BLOCKED (signature).** The mathematics closes for every `d ≥ 2` with nothing owed to G6a. The pin has no `3 ≤ d →` (`GreenCore.lean:1644`), and every merged ingredient needs `2 ≤ d`: `BAsum_exp_decay_le (hd : 2 ≤ d)` (`Prop5Short.lean:251`), `baM_row_l1`, `baM_rhohat`, `baTheta_weighted_l1` (`GreenStab.lean:116, 147, 251`). `d = 0` is vacuous (`size = (WL)^0 = 1`, so `BAFlow` is false); `d = 1` is not covered by any merged lemma (no 1D radial sum). Comparable pins carry the hypothesis inside (`BAProp5s`, `FlowPins.lean:185`; `BAKbound`, `KBound.lean:197`). Needed decision: `baGbEXPij'_holds (d) (hd : 3 ≤ d)` (or `2 ≤ d`) with the registry line kept or relabelled accordingly, or a primed pin `3 ≤ d → …`. Everything else in target 3 is PASS: `c = GreenStab_clam d 𝔡⁻¹ κ` depends on `(d,κ,𝔡)` only (order `c` after `(κ,ε,𝔡)`, before `ε₀`); the identity `‖𝓛^{(2)}_{(−,+),(a,b)}‖ = W^{-2d}Σ_{x∈a,y∈b}|G_xy|²` (rows in `a`) and the `Idx ↔ Vtx` relabelling are needed in `GreenOff` (the merged proofs of the identity are private to `Green/Pins.lean`).
- Paper-delta candidates: `T2403a`: the Lean pin `BAGbEXPij'` has no `3 ≤ d` (paper: `d ≥ 3`); `T2403b`: `(GijGEX_BA)` constant `c_λ` and the loss `N^{3τ₀/2}` per (table); the `W^{-D}` term is unused (as `T2390g`).

## (a′) Preflight corrections — Sun Oct 11 04:15:07 UTC 2026
Deviations of the compiled work from (a); none changes a verdict.  (1) (a)(i) bounds `sup|t v̄ − 𝒜'|` through (Ξ) (`η₁`, so (C2) needs `3τ₀/2 < 𝔠ε₀`).  Compiled: the row form of (A*), `|A_w| ≤ α = (2/κ)δ(2dg₀ + (1+2dg₀)/κ)` (`GreenOff_Arow_bd`; the merged `GreenCore_Acol_sq` is the column form), so `η = α + e_X + 2dg₀e^γe_X/c₀ ≤ K_η √P δ` and (C1), (C2) need only `τ₀ ≤ 𝔠ε₀`; the pin takes `τ₀ = min(τ/2, 𝔠ε₀)`, the loss stays `N^{3τ₀/2}`.  (2) (a)(ii)'s `BAReal` instance (`g₀ = 0.013`, `c₀ = 1`, `C_Θ̂ = 0.667`) rests on Python numbers: Lean has `c₀ = BAct_rate` (`BAMB_decay_large`) and the analytic `C_Θ̂ = GreenStab_CTheta` (`5.9e162` in (a)(i)); the compiled instance of `GreenOff_close` keeps `d = 3`, `L = 4`, `t = 1/2` and takes `M^{(B)} = mI` with its own constants ((d) O1-O2).  (3) (a) `C_T = max(·,·)`; compiled `C_T = 2c₀⁻¹√S + √(16ρPc₀⁻¹S)` (the sum, larger).

## (b) Stage 1b: script output — Sun Oct 11 04:15:07 UTC 2026 (claude-sonnet-5-5; branch `t/T2403` at `b160f1c`, file `RBM3D/BA/GreenOff.lean`)
**Size against the stop line 1,600** (`git show <c>:RBM3D/BA/GreenOff.lean | wc -l` at four section commits):
```
628 lines  9c33792 T2403: GreenOff section 1-2 (kernel, weighted closure GreenOff_close), WIP
1372 lines  d785732 T2403: baGbEXPij'_holds (target 3), WIP
1530 lines  75b8470 T2403: GreenOff target-1 instance, WIP
1568 lines  b160f1c T2403: BA-G4 GreenOff (weighted closure, baStab_holds, baGbEXPij'_holds, instances); registry: BAStab, BAGbEXPij' removed
```
**Builds** (worktree `RBM3D-wt/T2403`, 04:08:19 and 04:09:02 UTC by `date -u`):
```
$ lake build RBM3D.BA.GreenOff -> Build completed successfully (3790 jobs); no warning for GreenOff.lean
$ lake build                   -> Build completed successfully (4213 jobs)  [runs #assert_rbm_axioms]
$ lake env lean RBM3D.lean     -> exit 0 (`import RBM3D` + `#assert_rbm_axioms`): axiom audit: 11378 theorems, 3423 definitions, 0 axioms in `RBM`
$ grep -c "BAStab\|BAGbEXPij'" registry.out -> 0;  grep "sorry\|admit\|native_decide\|^axiom" GreenOff.lean | wc -l -> 0
```
**Registry** (Amend 1 D2): the pre-check passes with both owed lines removed, so the `BAGbEXPij'` line is removed (not relabelled), like `BAStab`.  `git diff main...t/T2403 -- RBM3D.lean RBM3D/Test/Axioms.lean`:
```
+import RBM3D.BA.GreenOff
-   `RBM.BA.BAStab, -- stability `‖(1 - t M^{(+,+)})⁻¹‖_{max→max} ≤ K` of the 
-   `RBM.BA.BAGbEXPij', -- `lem_GbEXP_BA` `(GijGEX_BA)` in the paper's shape, 
```
D3 (relabel `Test/Axioms.lean:133-135`) is not done (Amend 1 D3).  **Axioms** (`#print axioms RBM.BA.<n>` for the 51 public `theorem`/`def` names; 51 of 51 outputs are `[propext, Classical.choice, Quot.sound]`, 0 other):
```
'RBM.BA.GreenOff_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenOff_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStab_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenOff_carrier_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGbEXPij'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**Target statements** (script extraction; section variables `GreenOff.lean:262-301`: `{d L W : ℕ} [NeZero L] [NeZero W]`, `{Mb} {M D} {Δ 𝔛} {Ap} {vb}`, `{t γ Ψ P κ δ g₀ c₀ ρ S α N : ℝ} {φ}`):
```lean
-- GreenOff.lean:580-602
theorem GreenOff_close {Θ : Matrix (Zd d L) (Zd d L) ℂ} {CΘ : ℝ}
    (hc₀ : 0 < c₀) (hγ0 : 0 ≤ γ) (hγ : γ ≤ c₀ / 4) (hφ : ∀ a b, 0 ≤ φ a b)
    (hΨ : 0 < Ψ) (hΨw : Real.sqrt (((W : ℝ) ^ d)⁻¹) ≤ Ψ) (hP : 0 ≤ P) (hκ : 0 < κ) (hδ0 : 0 ≤ δ) (hg : 0 ≤ g₀)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hvb : ∀ a, vb a = (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, Δ (a, o) (a, o))
    (hE3 : ∀ x y, Δ x y = ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y +
      ((t : ℂ) * vb b' - Ap (b', x.2)) * Δ (b', x.2) y - Ap (b', x.2) * M (b', x.2) y - 𝔛 (b', x.2) y))
    (hX : ∀ u y, ‖𝔛 u y‖ ≤ Real.sqrt (2 * P) * ((1 + 2 / (κ * c₀)) * GreenCore_T d L W c₀ ρ S P φ u.1 y.1 +
      Real.sqrt 13 / κ * δ * ‖Δ u y‖))
    (hXi : ∀ w, ‖Ap w‖ ≤ Real.sqrt 13 / κ * δ * (1 + Real.sqrt (2 * P)) * GreenCore_T d L W c₀ ρ S P φ w.1 w.1 +
      Real.sqrt (2 * P) * φ w.1 w.1 + Real.sqrt (P * ((W : ℝ) ^ d)⁻¹) +
      Real.sqrt (2 * P) * ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀) * GreenCore_T d L W c₀ ρ S P φ w.1 w.1 +
        Real.sqrt 13 / κ * δ * ∑ l, ‖D l w‖ * ‖Δ w l‖))
    (hA : ∀ w, ‖(t : ℂ) * vb w.1 - Ap w‖ ≤ α)
    (hD1 : ∀ w, ∑ l, ‖D l w‖ = 2 * d * g₀) (hDadj : ∀ l w, D l w ≠ 0 → zdistD d L (w.1 - l.1) = 1)
    (hΘ : ∀ b a, Θ b a = (if b = a then 1 else 0) + (t : ℂ) * ∑ c, Θ b c * (Mb a c * Mb c a))
    (hΘw : ∀ b, ∑ a', ‖Θ b a'‖ * Real.exp (2 * γ * (zdistD d L (b - a') : ℝ)) ≤ CΘ)
    (hC2 : (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S * GreenOff_eta d κ c₀ P δ g₀ γ α) ≤ 1 / 2)
    (x y : Vtx d L W) :
    ‖Δ x y‖ ≤ 2 * GreenOff_Cl d κ c₀ ρ S P δ g₀ CΘ * GreenOff_T d L γ Ψ φ x.1 y.1 := by
-- GreenOff.lean:809-810
theorem baStab_holds (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : BAStab d L g E m t (16 * κ⁻¹ ^ 4) :=
-- GreenOff.lean:1289-1289
theorem baGbEXPij'_holds (d : ℕ) (hd : 2 ≤ d) : BAGbEXPij' d := by
```
`GreenOff_decay` (same file) is target 1 at the BA data: it derives `hdec` (`BAMB_decay_large`), `hS` (`BAsum_exp_decay_le`), `ρ` (`baM_col_l1`), `hX` (`GreenCore_Xstar`), `hXi` (`GreenCore_Xi`), `hA` (`GreenOff_Arow_bd`), `hE3` (`GreenCore_E3`), `Θ = BATheta … true true` (`BATheta_resolvent`, `baTheta_weighted_l1`), `γ = GreenStab_clam`, `C_Θ̂ = GreenStab_CTheta`.
**Instances** (compiled `example`s in namespace `RBM.BA.GreenOffInst`, script extraction):
```lean
-- GreenOff.lean:1517
example : ∀ x y : Vtx 3 4 W₁, ‖Δ₁ x y‖ ≤ 2 * GreenOff_Cl 3 (1 / 2) 1 1 64 1 δ₁ (1 / 64) 1 *
    GreenOff_T 3 4 (1 / 12) 1 (fun _ _ => (1 : ℝ)) x.1 y.1 := fun x y =>
-- GreenOff.lean:1526
example : ∃ x y : Vtx 3 4 W₁, Δ₁ x y ≠ 0 := ⟨default, default, by simp [Δ₁]⟩
-- GreenOff.lean:1530
example : GreenStabInst.vI 0 = 1 ∧ ‖GreenStabInst.vI 0‖ ≤ 16 * (1 / 2 : ℝ)⁻¹ ^ 4 * (3 / 2) := by
-- GreenOff.lean:1552
example : ∃ c : ℝ, 0 < c ∧ ∀ D : ℝ, 0 < D →
    GreenCore_loopPrem SizesInst.sz0 FlowPinsInst.zSeq (fun _ => 1 / 2) (1 / 10)
      (fun n _ _ => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ))) →
    GreenCore_decayConcl SizesInst.sz0 FlowPinsInst.zSeq (fun _ => 1 / 2) (1 / 10) D c
      (fun n _ _ => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ))) (fun n => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-1 : ℝ)) := by
```
Target 1: `d = 3`, `L = 4`, `W₁ = 10^5`, `t = 1/2`, `κ = 1/2`, `c₀ = 1`, `S = 64`, `ρ = 1`, `P = 1`, `g₀ = 1/64`, `D` the adjacency `g₀Ψ`, `M = mI` (`m = i`), `Δ = δ(1_{x=y} + ½1_{x≠y, o(x)=o(y)}) ≠ 0`, `δ = 10⁻⁶`, `𝒜' ≡ δ`, `𝔛 = −(δ/2)(M+Δ) + iΔ`, `φ ≡ 1`, `Ψ = 1`, `γ = 1/12`, `Θ = (2/3)I`, `C_Θ̂ = 1`, `α = δ`; all 25 hypotheses discharged.  `python3 inst_check.py`:
```
eta=1.2237e-05  (C2) lhs=(1+A)*rhohat*eta=0.0509 <= 0.5
C_T=48.0 s_X=339.4 s_A=43.3  2*C_l'=3.184e+06  (|Delta|<=1e-06, so the instance bound is valid but loose)
s2=sqrt(16*rho*P*S/c0)=32.0
```
Target 2: the flow datum of `sz0` at `n = 0` (`BAReal` by `BAflow_real`), `δ_0 ≠ 0` with its hypothesis proved.  Target 3: the data of the `example` at `GreenCore.lean:1659` with the pin proved; only the loop premise (the consumer's pin) stays a hypothesis.
**Names, ports, scope**: `grep -rln "GreenOff_\|baGbEXPij'_holds\|baStab_holds\|GreenOffInst" RBM3D RBM3D.lean` -> `RBM3D/BA/GreenOff.lean` only; the same grep in `../RBM1D/RBM1D ../RBM2D/RBM2D` -> no output.  No code from RBM1D/RBM2D (no diff-stat).  Private copies of RBM3D lemmas: `GreenOff_gres_blockMat_true/false`, `GreenOff_trace_pm`, `GreenOff_sum_vtx_ite` (`Green/Pins.lean:350, 367, 378, 1265`; `GreenOff_loop_eq` reproduces `:404, :494`), `GreenOff_W_rpow_neg_le`, `GreenOff_card_vtx/off`, `GreenOff_whp` (`Green/EntryDom.lean:777, 726, 733, 766`); `GreenOff_Arow_bd` adapts `GreenCore_Acol_sq` (`GreenCore.lean:796`).  `git diff --name-only main...t/T2403`: `RBM3D.lean`, `RBM3D/BA/GreenOff.lean`, `RBM3D/Test/Axioms.lean`.
**Narrative.**  Target 1 = `GreenOff_close`.  In the ratio norm `N = max|Δ_{xy}|/𝔗([x],[y])` (`Finite.exists_max`, `𝔗 > 0`): `GreenOff_R_bd` bounds `R = Δ − L3` by `(S₀ + η₀N)𝔗` (`GreenOff_X_bd`, `GreenOff_Ap_bd`, `hA`, kernel preservation `GreenOff_convA/convB` from `hdec`, `hS`, `GreenOff_T_shift`; the merged `baM_rhohat`, `baMfine_rhohat` are the same bound and are not used); `GreenOff_theta_step` solves `v̄ = Θu` (`GreenOff_vb_theta`), `|v̄_b| ≤ KC_Θ̂𝔗(b,b)`, bounds `L3`; at the maximiser `N ≤ (1+ρ̂c₀⁻¹C_Θ̂)(S₀+η₀N)` and (C2) gives `N ≤ 2C_ℓ'`.  `12γ ≤ c₀` (`GreenStab_clam_le_c0`) gives `T ≤ C_T𝔗_γ`; `baTheta_weighted_l1` gives the `Θ` weight.
Target 2: `baStab_holds` is `baStab_of_real` as the Prop `BAStab … (16κ⁻⁴)` (`GreenCore.lean:1268`).  Target 3: `c = GreenStab_clam d 𝔡⁻¹ κ`, order of quantifiers as the pin; for `(τ, D')` take `τ₀ = min(τ/2, 𝔠ε₀)`; the four events of `baLDEin_holds` (`≤ N²` pairs, `N` sites) and the loop premise (`StochDomAt.highProb`) hold with high probability jointly (`HighProbAt.inter`); on them and on `Ω` (`indMax = 1`) `GreenOff_carrier_decay` with `φ = N^{τ₀/2}Φ_n` (`GreenOff_loop_eq`) gives `|(G−M)_{xy}| ≤ 2C_ℓ'N^{τ₀/2}ζ ≤ K_clN^{3τ₀/2}ζ ≤ N^τζ` for `n` large (`GreenOff_pin_consts`, `GreenOff_ev_big/small`, `W ≥ N^𝔠`); if `Ω` fails `ξ = 0`.  The `W^{-D}` term is only dropped; no fluctuation averaging, no iteration.  Nothing is owed to G6a (the loop premise is the pin's own hypothesis; `baLDEin_holds` is unconditional); the constants depend on `(d, κ, 𝔡)` only (ticket C1/G2).

## (c) Verified Mathlib names (`#check`, exit 0; the other Mathlib names of the file type-check in the build; none searched absent)
`Real.sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2`; `Real.one_le_sqrt : 1 ≤ √x ↔ 1 ≤ x`; `Real.sqrt_le_one : √x ≤ 1 ↔ x ≤ 1`; `Real.sqrt_mul : 0 ≤ x → ∀ y, √(x*y) = √x*√y`; `Real.mul_self_sqrt : 0 ≤ x → √x*√x = x`; `Real.sqrt_eq_rpow : √x = x^(1/2)`
`tendsto_rpow_neg_atTop : 0 < y → Tendsto (fun x => x^(-y)) atTop (nhds 0)`; `tendsto_rpow_atTop : 0 < y → Tendsto (fun x => x^y) atTop atTop`; `ge_mem_nhds : b < a → ∀ᶠ x in nhds b, x ≤ a`; `Filter.Tendsto.eventually_ge_atTop`
`Real.rpow_le_rpow_of_nonpos : 0 < x → x ≤ y → z ≤ 0 → y^z ≤ x^z`; `Real.rpow_le_rpow_of_exponent_le : 1 ≤ x → y ≤ z → x^y ≤ x^z`; `Real.one_le_rpow : 1 ≤ x → 0 ≤ z → 1 ≤ x^z`; `Real.exp_one_lt_d9 : exp 1 < 2.7182818286`
`inv_le_one₀ : 0 < a → (a⁻¹ ≤ 1 ↔ 1 ≤ a)`; `div_le_div_of_nonneg_right : a ≤ b → 0 ≤ c → a/c ≤ b/c`; `le_of_mul_le_mul_right : b*a ≤ c*a → 0 < a → b ≤ c`; `mul_nonneg_iff_of_pos_right : 0 < c → (0 ≤ b*c ↔ 0 ≤ b)`
`Finite.exists_max : ∀ f, ∃ x₀, ∀ x, f x ≤ f x₀`; `Fintype.card_subtype_le`; `Matrix.trace_mul_comm : (A*B).trace = (B*A).trace`; `Matrix.conjTranspose_nonsing_inv : A⁻¹ᴴ = Aᴴ⁻¹`; `Matrix.inv_submatrix_equiv`; `Complex.I_mul_I : I*I = -1`; `MeasureTheory.measure_mono`

## (d) Open issues and paper-delta candidates
- O1: no concrete-`n` instance exists for `GreenOff_decay`, `GreenOff_carrier_decay` ((C2) with the analytic `C_Θ̂` is eventual).  `k2.py` (compiled constants at (a)'s datum, log₁₀ values of (a)'s table): `log10 K2 = 204.1  (K2=(1+A) rhohat K_eta, A=rhohat C_Theta/c0)  -> (C2) needs sqrt(P) delta <= 1/(2 K2)` / `tau0=c*eps0: sqrt(P) delta <= N^(-c*eps0/2)=N^(-0.00833): log10 N >= 24530`.  The pin instance shows the pin's statement at concrete data.
- O2: the instance of target 1 has `M = mI` and a `D` not tied to `M` (`GreenOff_close` links neither): it witnesses the joint satisfiability of the stated hypotheses (`t = 1/2`, `Δ ≠ 0`), not the BA kernel; its numeric conclusion is loose (`2C_ℓ' = 3.2e6` vs `|Δ| ≤ 1e-6`).
- O3: the loop premise `GreenCore_loopPrem` stays a hypothesis of the pin and its instance (consumer's pin at G7).  O4: D3 (supervisor `2026-10-11-0150` K1) not done.  O5: 1,568 of 1,600 lines.
- Paper-delta candidates (proposed): `T2403a` the Lean pin has no `d ≥ 3`, the theorem is for `2 ≤ d` (Amend 1 D1; harmless); `T2403b` the rate is `c_λ = min(BAct_rate/12, BAp5s_rate/6)` (as `T2390g`), the conclusion is proved with `zdistD ≥ zdistInf`, without the `W^{-D}` term, loss `N^{3τ₀/2}`, `τ₀ = min(τ/2, 𝔠ε₀)`; `T2403c` (a′) D3.1 `(A*)` `|𝒜_w| ≤ C_𝒜a` is the compiled row form `|A_w| ≤ α`, and the coefficients of (X*), (Ξ) are the merged ones (`T2390l`), so `C_η` of (a′) D3.4 is `GreenOff_eta`; `T2403d` target 1 is proved in the abstract form (merged pointwise bounds as hypotheses), `C_T = 2c₀⁻¹√S + √(16ρPc₀⁻¹S)`, (C2) of the shape `(1 + ρ̂c₀⁻¹C_Θ̂)ρ̂η ≤ 1/2`.
- Stage 1b result: targets 1, 2, 3 delivered and committed on `t/T2403` at `b160f1c` (the three sole writable files).
