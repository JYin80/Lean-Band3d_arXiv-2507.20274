Prover model: claude-sonnet-5-5
**Size against DECISIONS §52 (BA cap 70), group BA-DS: BA total = 57 (T2161) + 5 new (BA-C1..C5; lo 4, hi 9) - 0 replaced = 62 (61..66) if the UN GUE-phase tickets UN-25..52 are written model-generic (portmap P.3, P.4); 75 (71..82) > 70 if they stay band-only (BA must twin all 28).  UN becomes 52 + 1 (UN-01b) = 53 (cap 60; T2162's count, later splits such as UN-02a not counted).  The dispatcher fixes the form of UN-25..52 before they are written; Jun is asked only if the BA total exceeds 70.**
## Top notices (T2173, stage 1b, Mon Oct  5 06:34:22 UTC 2026; section (a) below is unchanged)
1. **The OU flow of the block Anderson model must be the centred flow `λΨ + e^{-t/2}V + √(1-e^{-t}) H'`.**  The T2162 matrix `ouMat = e^{-t/2}H + √(1-e^{-t})H'` has the mean `e^{-t/2}λΨ`; the generator identity gets the drift `-½e^{-t/2} 𝔼 dΦ[λΨ]` (-309.35 against -1.66 for the second-order term at `(λ, t) = (0.3, 0.7)`, b.5) and its naive bound (0.745, 16.8) does not decay against `N^{-c'+Cτ_U}` (`C = C_max = 21`, (a)).  This amends the merged UN-01 (T2174, `Universality/Pins.lean`): `UNModel` gets `mean`, `ouMat` is centred (A1), Step 1 reads `ouInit` (A2); `mean = 0` gives the T2162 matrix (`ouMat_band`).  Main has since merged UN-08 (T2175) and UN-02a (T2177): against main `a52eb85` the amendment compiles with 6 changed names in `Pins.lean` and 3 changed lines in `OU.lean`, the other merged files compile unchanged (b.1a); new ticket UN-01b.  The BA flow minus `λΨ` is the band flow of `sz.withLam 0` (`ouMat_ba_eq_band_add`): the merged `ouSample_law` serves BA (`ouSample_law_ba`, b.1a).
2. **T2173a**: T2161 states its block Anderson pins under `sz.seqP` (38 lines with `Prec sz` or `sz.seqP` in the probe at `82e72b3`), whose Gaussian part has the band profile `S^{(B)}(lam)`; the BA law is `(sz.withLam 0).seqP` (compiled witness `seqGvar_ne_withLam_zero`).  **T2173b**: `BAGlueUniv` (T2161 `:1847`) has no `BAEnd_QUE` and no BA-V3 flow outputs, which the OU rows consume.  **T2173d**: the BA density regularity `UNDens` (uniform modulus of `m(z, λ)`) is not among T2161's pins (new BA-C2).
## (a) Math preflight — Mon Oct  5 04:40:53 UTC 2026
Notation: `g` = `λ` of the ticket (paper `\ilambda`); `d = 3`; `N = (WL)^3`; `Ψ = Ψ^(B) ⊗ I_{W^3}` (1_2:615-616); `V` block-diagonal GUE, `S^V_{xy} = W^{-d} 1(a=b)` (`bandcwV`, 1_2:606); `H = V + λΨ` (1_2:611); `S° = S^V − 1/N`; `t* = N^{-1+τ_U}`; `ρ_N = π⁻¹ Im m(E+i0)`, bulk set `ρ_N ≥ κ` (DECISIONS §51, `BAbulk`). Scripts (python3/numpy, no Lean) in `…/scratchpad/T2173/`: `pre.py`, `drift.py`, `size.py`, `dens.py`, `inst.py`.
### (i) Exponent table (d = 3; W-powers unless stated; two admissible `(𝔠,𝔡)`: `(1/6,1/10)`, `(1/10,1/20)`)
| quantity | value | constraint (source) | slack |
|---|---|---|---|
| `𝔠` | 1/6; 1/10 | `W ≥ N^𝔠` ⇔ `L ≤ W^{(1−3𝔠)/(3𝔠)}`, so `𝔠 < 1/3` (L ≥ 3) | `L ≤ W^1`; `L ≤ W^{7/3}` (printed); `W=32, L=5`: 32 ≥ 12.65; 4.58 |
| `𝔡`, `λ` | 1/10; 1/20 | `W^{-3/2+𝔡} ≤ λ ≤ 𝔡^{-1}` (eq:WO); `λ=10` needs `𝔡 ≤ 1/10` | `λ=10` is the boundary row at `𝔡=1/10` (equality); `λ=0.3`: factor 33 below 𝔡⁻¹=10 |
| `ε₀ = 𝔡/3` | 1/30; 1/60 | `0 < ε₀ < 𝔡/2` (1_2:407) | `𝔡/6` |
| `c = 𝔡/6` | 1/60; 1/120 | `0 < c < ε₀ ∧ 𝔡/5` (1_2:410) | `𝔡/6` (vs ε₀); `𝔡/30` (vs 𝔡/5) |
| QUE exponent | `−(2ε₀∧2𝔡/5)+2c = −𝔡/15` | matches 1_2:577 (`QUE=-1/150`, `-1/300`) | `τ_Q = 𝔡/30` leaves `W^{-𝔡/30}` |
| 𝓑(y) window | `N^{-1}W^{𝔡/3} ⊂ 𝓘_E(ε₀)`, half-width `W^{-ε₀}λW^{3/2}/N ≥ W^{2𝔡/3}/N` | (eq:defIE) 1_2:408; BA window has `λ`, not `λ∧1` (T2161 `BAqueWindow`) | ratio window/𝓑-window ≥ 43 (λ=0.3), ≥ 1436 (λ=10) at W=32 (script (ii)) |
| window in N-scale | `−1 + (𝔡/3) log_N W ∈ [−1+𝔠𝔡/3, −1+𝔡/9)` | `> −1`, `< 0` | `[−179/180, −89/90)`; `[−599/600, −179/180)` |
| `θ` (|M_{y,α}| threshold) | `W^{-𝔡/6}` = `N^{-𝔠𝔡/6}` | `M_{y,α}` normalised as the QUE quantity `(N/W^d)Σ_{x∈[a]}|ψ|²−1` | `BAqueBad` (i=j) threshold `W^{d-c}/N ≤ |Σ_{x∈[a]}|ψ|²−W^d/N|` ⇔ `|M| ≥ W^{-c}` (T2161 probe); identity checked: 2.9e-15 (`inst.py` (b)) |
| `ℙ(𝓑)` (BA) | `≤ 1·W^{-𝔡/15+τ}`: **one** block (`S^V` row support = 1 block; band d=3: `2d+1 = 7`) | 1_2:577 | `N^{-𝔠(𝔡/15−τ_Q)} = N^{-𝔠𝔡/30}`: 1/1800, 1/6000 |
| `c'` (Claim 417) | `min(𝔠𝔡/6, 𝔠𝔡/30) = 𝔠𝔡/30` (ℙ(𝓑) binds, as band, T2162 (a)) | `c' > 0` | 1/1800; 1/6000 |
| `τ_U` | `≤ c'/(2(C_max+1))`, `C_max = 21` (RBM2D constants, T2162 (a); to be redone at d = 3) | whether `C_max` depends on `κ`, `λ` at d = 3 is open (stage 1b) | 1/79200; 1/264000. At N=216: `t* = 0.00462994` (1/N = 0.00462963), `N^{-c'+Cτ_U} = 0.99844` |
| OU generator (non-centred `ouMat`) | `d/dt E f(H_t) = −½e^{-t}ΣS°_{ab}E∂_{ab}∂_{ba}f − ½e^{-t/2}λ E⟨Ψ,∇f⟩`; RBM2D `OUGenerator.lean:940` (c9a24cf, mean-zero `P`) has only the first term | drift coefficient `λ‖Ψ‖/2 = dλ` | centred flow `H̃_t = λΨ + e^{-t/2}V + √(1−e^{-t})H'`: drift = 0 exactly |
| naive drift bound | `∫₀^{t*}` drift `≤ dλ·Im m·t*/η`, `η ∈ [N^{-1-τ_U}, N^{-1+τ_U}]`, `t*/η ≥ 1`: N-independent | must be `≤ N^{-c'+Cτ_U} < 1` | **negative**: 0.732 (λ=0.3), 19.3 (λ=10) at `η=t*` (script `size.py`); sampled value at N=216 is 0.0062, 0.0003 but no N-scaling mechanism: BA local law (`G_bound`, `G_bound_ave`, 1_2:391-399; BA domain 7_8:1817) is for `η ≥ N^{-1+ε}`, and the averaged form is on block diagonals only |
| endpoint density (Step 1) | centred: `ν̄_A ⊞ sc_s` with `A = λΨ + e^{-t*/2}V`, `s = 1−e^{-t*}`: variances `e^{-t*}+s = 1`, so `m' = m(z,λ)` exactly (`≤ 8.0e-15` at `t = 4.6e-3, 0.05, 0.5`); non-centred: `m(z, λe^{-t/2})`, shift `4.4e-4` at `t=4.6e-3` (`≈ 0.63·t*λ/2`) | centred needs the BA local law at `λ' = λe^{t*/2}` (admissible with `𝔡' < 𝔡`); non-centred needs Lipschitz of `ρ_N` in `λ` (new) | exact vs `O(t*)` |
| `UNDens` data (κ = 0.05) | on `|E'−E| ≤ 0.025`: `min ρ ≥ 0.0574`, `Lip ≤ 0.353`; `c ≤ Im m ≤ C` over `η ∈ [1e-9,1]`: `c = 0.124…0.549`, `C = 0.228…0.828` | `c` is **not** `πκ` (row (5,10): `c = 0.124 < πκ = 0.157` though `πρ_N(E) = 0.206`) | `δ` depends on `Lip`, uniformly in `(L_n,λ_n)`: new input |
| `κ`-dependence (D403) | exponents `κ`-free; constants not: `Lip ρ_N` at the cusp `L=4, λ=g_c`: 0.21, 0.65, 2.12 at κ = 0.1, 0.05, 0.025 (≈ κ^{-1.7}); `min_k|1−M^{++}_k|` shrinks (0.870, 0.591, 0.418 at κ = 0.15, 0.05, 0.02, L=5, λ=0.3); `1−|m|²` (0.389–0.536) and the gap of `1−M^{+-}` (0.19–0.38) stay positive in this range (`pre.py`) | `lem:propM`(2) uses `Im m ≳ 1` (7_8:1908, D403) | constants → ∞ as κ → 0, fixed κ in every pin (`∀ κ > 0`) |
| `λ → 0` (extreme) | `ρ_N(0) = 0.318310 = 1/π` at `λ = 1e-6`; drift `= 0` (Wick rows `λ=0`: non-centred = centred) | BA rows reduce to the band-type statement with profile `S^(B)(0) = I` | exact |
### (ii) One concrete nondegenerate instance (d = 3)
Data: `W = 32`, `L ∈ {4,5}` (`N = 2097152`, `4096000`), `λ ∈ {0.3, 10}`, `(𝔠,𝔡)` as above, `κ = 0.05`, `E` = bulk-set point nearest 0 (`E = 0` except `(L,λ) = (5,10)`: `E = −3.048`, since `ρ_N(0) = 5.4e-12`: `E = 0` is in a gap). All hypotheses (Admissible, (eq:WO), `ρ_N(E) ≥ κ`, window ⊂ `𝓘_E`) hold simultaneously; the `ℙ(𝓑)` bound is a conclusion (`eventually`), not a hypothesis.
`$ python3 pre.py` (exponents exact; the 8 instance rows; κ-dependence; `λ → 0`):
```
c=1/6 d=1/10: eps0=1/30 (<d/2=1/20) c_Q=1/60 (<eps0, <d/5=1/50) QUE=-1/150 (=-d/15: True) tauQ=1/300 theta_exp(N)=1/360 PB_exp(N)=1/1800 c'=1/1800 tauU<=1/79200 | N-window [-179/180,-89/90) | lam range W^{-3/2+d}..d^-1 = ..10 | L<=W^1
c=1/10 d=1/20: eps0=1/60 (<d/2=1/40) c_Q=1/120 (<eps0, <d/5=1/100) QUE=-1/300 (=-d/15: True) tauQ=1/600 theta_exp(N)=1/1200 PB_exp(N)=1/6000 c'=1/6000 tauU<=1/264000 | N-window [-599/600,-179/180) | lam range W^{-3/2+d}..d^-1 = ..20 | L<=W^7/3
c=1/6 d=1/10 L=4 lam=0.3  N=2097152 | W>=N^c:True (32.00>=11.31) WO:True (0.0078<=lam<=10.0) E=0.000 rho_N(E)=0.2636>=k:True res=4.7e-15 | QUE-halfwidth*N=48.38 >= Bwin*N=1.122 (ratio 43.10): True | ok=True
c=1/6 d=1/10 L=4 lam=10   N=2097152 | W>=N^c:True (32.00>=11.31) WO:True (0.0078<=lam<=10.0) E=0.000 rho_N(E)=0.1781>=k:True res=3.7e-19 | QUE-halfwidth*N=1612.70 >= Bwin*N=1.122 (ratio 1436.75): True | ok=True
c=1/6 d=1/10 L=5 lam=0.3  N=4096000 | W>=N^c:True (32.00>=12.65) WO:True (0.0078<=lam<=10.0) E=0.000 rho_N(E)=0.2624>=k:True res=2.9e-15 | QUE-halfwidth*N=48.38 >= Bwin*N=1.122 (ratio 43.10): True | ok=True
c=1/6 d=1/10 L=5 lam=10   N=4096000 | W>=N^c:True (32.00>=12.65) WO:True (0.0078<=lam<=10.0) E=-3.048 rho_N(E)=0.0657>=k:True res=9.9e-15 | QUE-halfwidth*N=1612.70 >= Bwin*N=1.122 (ratio 1436.75): True | ok=True
c=1/10 d=1/20 L=4 lam=0.3  N=2097152 | W>=N^c:True (32.00>=4.29) WO:True (0.0066<=lam<=20.0) E=0.000 rho_N(E)=0.2636>=k:True res=4.7e-15 | QUE-halfwidth*N=51.26 >= Bwin*N=1.059 (ratio 48.38): True | ok=True
c=1/10 d=1/20 L=4 lam=10   N=2097152 | W>=N^c:True (32.00>=4.29) WO:True (0.0066<=lam<=20.0) E=0.000 rho_N(E)=0.1781>=k:True res=3.7e-19 | QUE-halfwidth*N=1708.60 >= Bwin*N=1.059 (ratio 1612.70): True | ok=True
c=1/10 d=1/20 L=5 lam=0.3  N=4096000 | W>=N^c:True (32.00>=4.58) WO:True (0.0066<=lam<=20.0) E=0.000 rho_N(E)=0.2624>=k:True res=2.9e-15 | QUE-halfwidth*N=51.26 >= Bwin*N=1.059 (ratio 48.38): True | ok=True
c=1/10 d=1/20 L=5 lam=10   N=4096000 | W>=N^c:True (32.00>=4.58) WO:True (0.0066<=lam<=20.0) E=-3.048 rho_N(E)=0.0657>=k:True res=9.9e-15 | QUE-halfwidth*N=1708.60 >= Bwin*N=1.059 (ratio 1612.70): True | ok=True
all rows ok: True

== kappa-dependence: stability quantities at E_k = largest of 400 grid points in [0,2+6 lam] with rho_N>=k (L=5, lam=0.3) ==
L=5 lam=0.3  k=0.15 E_k=1.9238 rho=0.1510 | 1-|m|^2=0.3888 min_k|1-M++_k|=0.8704  lam0(1-M+-)=2.1e-09  lam1(1-M+-)=0.1939
L=5 lam=0.3  k=0.05 E_k=2.4571 rho=0.0502 | 1-|m|^2=0.5188 min_k|1-M++_k|=0.5908  lam0(1-M+-)=6.3e-09  lam1(1-M+-)=0.3848
L=5 lam=0.3  k=0.02 E_k=2.5905 rho=0.0201 | 1-|m|^2=0.5360 min_k|1-M++_k|=0.4183  lam0(1-M+-)=1.6e-08  lam1(1-M+-)=0.3419

lam=1e-6 L=4: rho_N(0)=0.318310 vs rho_sc(0)=1/pi=0.318310
```
Generator identity at `d=3, L=3, W=2` (`N = 216`, blocks `W^d = 8`, 27 blocks, `‖Ψ‖ = 6`): `$ python3 drift.py mc 6000` (A: exact Wick, `f = Tr H⁴`; B: 6000 Monte-Carlo samples, `f = Im N⁻¹Tr G(z)`):
```
A0. D_ij D_ji Tr H^4: finite difference 225.761239+0.000000j vs formula 225.761239+0.000000j
A. exact Wick, f = Tr H^4:  d/dt E f (central difference of closed form)  vs  generator RHS
   lam   flow        t     LHS             RHS(drift+gen)   drift term       RHS w/o drift    LHS-RHS
   0     non-centred 0.7  -1.66306266     -1.66306264      -0.00000000      -1.66306264      -2.09e-08
   0     centred     0.7  -1.66306266     -1.66306264      0.00000000       -1.66306264      -2.09e-08
   0.3   non-centred 0.7  -311.01019068   -311.01019064    -309.34712800    -1.66306264      -3.62e-08
   0.3   centred     0.7  -1.66306266     -1.66306264      0.00000000       -1.66306264      -2.09e-08
B. Monte Carlo (M=6000 samples), f = Im N^{-1}Tr G(z), mean +- standard error
 lam=0.3  z=(0.2+0.5j) t=0.7
   non-centred: LHS +0.05472 +- 0.00006 | gen -0.00021 +- 0.00000 | drift +0.05486 +- 0.00002 | LHS-(gen+drift) +0.00007 +- 0.00007 | LHS-gen +0.05493 +- 0.00006
   centred    : LHS -0.00011 +- 0.00006 | gen(=RHS) -0.00018 +- 0.00000 | LHS-RHS +0.00007 +- 0.00006
 lam=0    z=(0.2+0.5j) t=0.7
   non-centred: LHS -0.00030 +- 0.00010 | gen -0.00025 +- 0.00001 | drift +0.00000 +- 0.00000 | LHS-(gen+drift) -0.00004 +- 0.00010 | LHS-gen -0.00004 +- 0.00010
   centred    : LHS -0.00030 +- 0.00010 | gen(=RHS) -0.00025 +- 0.00001 | LHS-RHS -0.00004 +- 0.00010
```
Size of the drift at `t* = N^{-1+τ_U}` (`$ python3 size.py`; sample = mean over 300 draws of `(λ/2)|Im N⁻¹Tr ΨG²|` at `t = 0`), regularity, endpoint density and `M_{y,α}` (`$ python3 dens.py; python3 inst.py`):
```
c'=0.000555556 tau_U=1.26263e-05 (1/79200=1.26263e-05) t*=N^{-1+tau_U}=0.00462994 (1/N=0.00462963)  N^{-c'+C tau_U}(C=21)=0.99844
lam=0.3  E=0.2 eta=0.00463 | Im m=0.813 | sample (lam/2)|Im N^-1 Tr Psi G^2|: mean 1.346 max 7.212 | naive (lam/2)||Psi|| Im m/eta = 158.1 | x t*: sample 0.00623, naive 0.732
lam=0.3  E=0.2 eta=0.50000 | Im m=0.663 | sample (lam/2)|Im N^-1 Tr Psi G^2|: mean 0.08024 max 0.08877 | naive (lam/2)||Psi|| Im m/eta = 1.194 | x t*: sample 0.000372, naive 0.00553
lam=10   E=0.2 eta=0.00463 | Im m=0.644 | sample (lam/2)|Im N^-1 Tr Psi G^2|: mean 0.06986 max 0.4417 | naive (lam/2)||Psi|| Im m/eta = 4170 | x t*: sample 0.000323, naive 19.3
lam=10   E=0.2 eta=0.50000 | Im m=0.457 | sample (lam/2)|Im N^-1 Tr Psi G^2|: mean 0.0004299 max 0.0005899 | naive (lam/2)||Psi|| Im m/eta = 27.39 | x t*: sample 1.99e-06, naive 0.127
UNDens-type data on [E-delta, E+delta], kappa = 0.05 (rho_N = Im m/pi at eta = 1e-9)
  L=4 lam=0.3  E=+0.000 delta=0.025: min rho=0.2636 (>= kappa/2=0.025: True) max rho=0.2636 Lip(rho)=0.001
  L=4 lam=10   E=+0.000 delta=0.025: min rho=0.1780 (>= kappa/2=0.025: True) max rho=0.1781 Lip(rho)=0.004
  L=5 lam=0.3  E=+0.000 delta=0.025: min rho=0.2623 (>= kappa/2=0.025: True) max rho=0.2624 Lip(rho)=0.002
  L=5 lam=10   E=-3.048 delta=0.025: min rho=0.0574 (>= kappa/2=0.025: True) max rho=0.0726 Lip(rho)=0.353
LSY (2.5)-type band c <= Im m(E'+i eta) <= C, |E'-E|<=0.025, eta in [1e-9,1] (log grid, 40 pts x 21 E'): and rho_N(0) at (L=5, lam=10)
  L=4 lam=0.3  E=+0.000: c=min Im m=0.5490  C=max Im m=0.8282  (pi*kappa=0.1571)
  L=4 lam=10   E=+0.000: c=min Im m=0.2513  C=max Im m=0.5594  (pi*kappa=0.1571)
  L=5 lam=0.3  E=+0.000: c=min Im m=0.5481  C=max Im m=0.8243  (pi*kappa=0.1571)
  L=5 lam=10   E=-3.048: c=min Im m=0.1242  C=max Im m=0.2280  (pi*kappa=0.1571)
  rho_N(0) at L=5, lam=10 (E=0 is in a gap): 5.40e-12
cusp (L=4, lam = g_c = 0.3542263, E* = 2.50792 from T2161 (a)): Lipschitz constant of rho_N at the point where rho_N = kappa
  rho_N(E*=2.50792)=0.0017
  kappa=0.100: E=2.33000 rho=0.1000 Lip=|rho'|=0.21  Lip*kappa^2=0.002
  kappa=0.050: E=2.47951 rho=0.0500 Lip=|rho'|=0.65  Lip*kappa^2=0.002
  kappa=0.025: E=2.50374 rho=0.0250 Lip=|rho'|=2.12  Lip*kappa^2=0.001
(a) L=4 lam=0.3 z=0.2+0.3i
  t=0.5: m(z,lam)=-0.0613034481+0.7253571074j | centred fc-endpoint -0.0613034481+0.7253571074j (|diff|=8.0e-15) | non-centred = m(z,lam e^{-t/2}) |diff|=4.171e-02  (t*lam/2 = 7.500e-02)
  t=0.05: m(z,lam)=-0.0613034481+0.7253571074j | centred fc-endpoint -0.0613034481+0.7253571074j (|diff|=7.7e-15) | non-centred = m(z,lam e^{-t/2}) |diff|=4.695e-03  (t*lam/2 = 7.500e-03)
  t=0.00463: m(z,lam)=-0.0613034481+0.7253571074j | centred fc-endpoint -0.0613034481+0.7253571074j (|diff|=7.0e-15) | non-centred = m(z,lam e^{-t/2}) |diff|=4.396e-04  (t*lam/2 = 6.945e-04)
(b) BA, N=216: max_alpha |M_{y,alpha} - (N/W^d) sum_{x in [a(y)]}|psi|^2 + 1| = 2.89e-15 ; #blocks in support of S°_{.y} = 1 (band d=3: 2d+1 = 7)
```
External hypothesis `UNL32` (LSY Thm 2.2, borrowed; DECISIONS §5): unchanged for BA (premises involve only `N`, `τ`; the model enters through the density sequence `ρ_n` and the regularity `c ≤ Im m ≤ C`, printed above); its limit computation (`σ = min(τ/4,(1−τ)/3)`; `g N^σ ≤ t ≤ N^{-σ}G²`; premises in `N`, `τ` only) is in `docs/reports/T2162-prove.md` (a)(ii), RBM2D `Pins.lean:156`. The BA-specific premise is the regularity `c ≤ Im m(·,λ) ≤ C` of the deterministic equivalent, with `c, C > 0` at every row (printed above).
### Verdict per target
Findings for stage 1b. F1: BA `M_{y,α}` is the one-block QUE quantity (union of 1 block, not 2d+1). F2: the OU flow of the whole `H` has the first-order drift `−½e^{-t/2}λ⟨Ψ,∇f⟩` (identity verified: Wick, MC); its naive bound is N-independent, so it is not an absorbable error; the centred flow (mean `λΨ` fixed) has no drift and keeps `ρ_N` exactly. F3: `E = 0` can lie in a gap (`L=5, λ=10`), and the density constant `c` is not `πκ`.
1 Interface: PASS (hypotheses hold in (ii); `UNClaim417/UNClaimAll/UNApriori/UNGreenCorr` are model-abstract; `UNEMCTE2/UNJak/UNUyw/UNOUQUE/UNOUDiag` need a BA form: `scirc` at variance coupling `0`, QUE window at `λ`, bulk set `BAbulk`, and the OU matrix with an explicit mean `λΨ`).
2 Drift: PASS with the route fixed to the centred flow; the non-centred route with the naive error bound FAILS (0.732 and 19.3 vs `< 1`, N-independent).
3 GUE phase: not testable at preflight (file level); no exponent conflict found (`c'`, `τ_U` unchanged; `ℙ(𝓑)` has 1 block).
4 Exponent table: PASS (every row closes, slack in the table). 5 Split table: not testable here. 6 Instances: PASS (nonempty, nondegenerate at `d = 3`).
Overall: **PASS**.

## (b) Script output — Mon Oct  5 06:34:22 UTC 2026; probe `RBM3D/Probe/T2173Pins.lean` (branch `t/T2173`, commit `a543154`, base `7738afa`); tables, split, scripts: `docs/reports/T2173-portmap.md` (P.1-P.7)
### b.1 Build, axioms, hygiene
```
$ git log --oneline 7738afa..HEAD; git diff --name-only 7738afa HEAD; git status --short | wc -l
a543154 T2173: probe: block Anderson form of Claim (417): centred OU flow, BA rows, derivation of UNClaimAll
RBM3D/Probe/T2173Pins.lean
       0
$ lake env lean RBM3D/Probe/T2173Pins.lean > lean.out 2>&1; echo exit=$?; grep -vc "depends on axioms" lean.out; tail -2 lean.out   (acceptance command; non-axiom lines; tail)
exit=0
0
'RBM.Univ.BAInst.seqGvar_ne_withLam_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.BAInst.inst_UNOUQUEk_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build RBM3D.Probe.T2173Pins > build.out 2>&1; tail -1 build.out; grep -c "warning: RBM3D/Probe\|^error" build.out; grep -c "^warning: RBM3D/Defs/Tail" build.out
Build completed successfully (3329 jobs).
0
3
$ grep "depends on axioms" lean.out | sed "s/.*axioms: //" | sort | uniq -c
 149 [propext, Classical.choice, Quot.sound]
$ echo "$(grep -cE 'sorry|admit|native_decide|^axiom' T2173Pins.lean) / $(grep -c '^import RBM3D' T2173Pins.lean) / $(wc -l < T2173Pins.lean)"   (hygiene hits / imports / lines)
0 / 9 / 4045
$ python3 verify_verbatim.py   (every block copied from t/T2162, t/T2161 against `git show <branch>:RBM3D/Probe/...`)
t62: 10 blocks, 1063 lines, identical 1063, differing 0
t61: 15 blocks, 1123 lines, identical 1123, differing 0
differing blocks: []
T2162 line ranges not copied: header, amended model/OU (95-164), unused sections: [(1, 46), (95, 164), (230, 230), (363, 363), (597, 597), (721, 721), (782, 782), (883, 883), (956, 1123), (1287, 1287), (1355, 2042)]
$ python3 clash.py   (declared names of the probe against every non-Probe file of RBM3D)
declared names of the probe: 326 (in the T2162 probe 83, in the T2161 probe 112, new in T2173 131)
worktree base 7738afa: clashes 0; files {}; of the new names 0; amended names []
main a52eb85: clashes 83; files {'Universality/Pins.lean': 83}; of the new names 0; amended names ['UNModel', 'UNModel.ba', 'UNModel.band', 'ouMat', 'ouMat_isHermitian', 'ouMat_zero']
```
### b.1a Amendment A1 against the merged files (`amend_check.py`: the probe's block of `UNModel`..`ouMat_zero` spliced into the merged `Pins.lean`, scratch modules)
```
merged files that mention ouMat, UNModel or ouP at main a52eb85: ['RBM3D/Universality/EigenMeasurable.lean', 'RBM3D/Universality/OU.lean', 'RBM3D/Universality/Pins.lean']
main a52eb85: Universality/Pins.lean lines 97-164 (UNModel .. end OU) replaced by T2173Pins.lean lines 113-201
PinsA (merged Pins.lean, 1921 lines): rc=0, errors 0
OU.lean unchanged: rc=1, errors 2
repair of OU.lean: 3 lines removed, 3 added
OU.lean repaired: rc=0, errors 0
EigenMeasurable.lean unchanged: rc=0, errors 0
GUEInvariance.lean unchanged: rc=0, errors 0
BA corollaries (probe lemmas ouMat_ba_eq_band_add, ouP_ba_eq_band; ouMat_ba_coord; ouSample_law_ba = merged ouSample_law at sz.withLam 0): rc=0, errors 0
```
### b.2 Targets: statements extracted by script (`statements.py`)
```
-- T2173Pins.lean:2496
theorem un_claimAll_of_rowsBA (rC : UNClaimRowBA) (rE : UNEMCTE2RowBA) (rJ : UNJakUywRowBA) (rO : UNOURowBA)
    (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → UNClaimAll sz (UNModel.ba sz) E :=
-- T2173Pins.lean:3620
theorem inst_claimAll_ba (huniq : BAmUniqReal 3)
    (rC : UNClaimRowBA) (rE : UNEMCTE2RowBA) (rJ : UNJakUywRowBA) (rO : UNOURowBA)
    (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) :
    UNClaimAll S0 (UNModel.ba S0) (fp 4 hg_3_10').E :=
-- T2173Pins.lean:179
def ouMat (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  M.mean n + Real.exp (-t / 2) • (M.H n ω.1 - M.mean n) +
    Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2
-- T2173Pins.lean:2666
theorem drift_entry (M : UNModel sz) (n : ℕ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n))
    (i j : Idx d (sz.L n) (sz.W n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (ouMatNC M n s ω - ouMat M n s ω) i j)
      (((-(1 / 2) * Real.exp (-t / 2) : ℝ) : ℂ) * M.mean n i j) t := by
-- T2173Pins.lean:2746
theorem ouMat_ba_eq_band_add (sz : Sizes d) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMat (UNModel.ba sz) n t ω - ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) =
      ouMat (UNModel.band (sz.withLam 0)) n t ω := by
-- T2173Pins.lean:3256
theorem UNQueBA_of_BAEnd_QUEL (h : ∀ d : ℕ, BAEnd_QUEL d) : UNQueBA := by
```
### b.3 Each new pin against the T2162 pin it modifies (`pin_diff.py`, differing lines / lines; literal changed lines: portmap P.1, `pin_diff_lines.py`)
```
T2162 pin              line   | probe pin              line   | differing lines of the declaration (whitespace-normalised)
UNOUQUE                636    | UNOUQUEk               2275   | 4 of 7 lines differ
UNEMCTE2               668    | UNEMCTE2k              2296   | 10 of 18 lines differ
UNJak                  693    | UNJakk                 2316   | 7 of 11 lines differ
UNQueBand              403    | UNQuek                 2378   | 3 of 6 lines differ
UNMLOut                431    | UNMLOutBA              2414   | 5 of 5 lines differ
UNStep1Good            583    | UNStep1GoodC           2553   | 4 of 12 lines differ
UNCore                 759    | UNCoreC                2570   | 3 of 8 lines differ
UNModel                103    | UNModel                119    | 4 of 8 lines differ
ouMat                  149    | ouMat                  179    | 2 of 3 lines differ
$ python3 pin_diff_lines.py ouMat
== ouMat (T2162 :149) -> ouMat (:179)
- Real.exp (-t / 2) • M.H n ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2
+ M.mean n + Real.exp (-t / 2) • (M.H n ω.1 - M.mean n) +
+ Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2
```
At `K = UNKind.band d` the five pins and the consumed QUE, `(G_bound_ave)` and the OU row are the T2162 pins: `UNOUQUEk_band`, `UNOUDiagk_band`, `UNEMCTE2k_band`, `UNJakk_band`, `UNUywk_band`, `UNQuek_band`, `UNLocAvgk_band`, `UNOURowk_band` (all `Iff.rfl`).
### b.4 Compiled instances at d = 3 and extreme inputs (data: `S0 = clsS 4 _ (3/10)`, `(𝔠, 𝔡) = (1/6, 1/10)`, `κ_* = clsκ`, `E_* = (fp 4 _).E` with `cls_bulk`; `sz0` with `flow_sz0`)
`inst_UNOUQUEk inst_UNOUDiagk inst_UNEMCTE2k inst_UNJakk inst_UNUywk inst_UNQueBA inst_locAvg_domain inst_UNLocAvgBA inst_UNMLOutBA` 
`inst_UNOURowBA inst_UNEMCTE2RowBA inst_UNJakUywRowBA inst_claimAll_ba inst_univ_ba inst_UNStep1GoodC inst_UNOUQUEk_zero` 
`inst_admissible_lamHat inst_shift_absorb inst_drift_not_absorbable inst_ba_mean_ne_zero inst_drift_ne_zero` 
`inst_badYBA_subset inst_badYBA_measure inst_que_exponent_ba inst_que_params_ba inst_cprime_ba inst_claim_exponent_ba inst_window_sub_ba` 
`inst_claimAll_ba`: `UNClaimAll S0 (UNModel.ba S0) E_*` from the BA rows, every deterministic hypothesis discharged (admissibility `S0_adm`, `κ_* > 0`, `E_*` in `{ρ_N ≥ κ_*}`); `inst_univ_ba`: `UNUnivDilAt S0 (UNModel.ba S0) (ρ_N(E_*)) E_* 0 1 bump` from `UNCoreC` and the rows (nonvacuity: `bump_nondegenerate`, `inWindow_nonempty`, `inst_ba_mean_ne_zero`: the drift direction `λΨ` has an entry `g₀ ≠ 0`).  Hypotheses kept (other gates' pins): the rows, the consumed inputs, `UNCoreC`, `UNL32`, `UNGUELocal`, `UNGreenCorrAll`, `BAmUniqReal 3`, `BAmExists 3`.  The instances are named theorems (no `example`) so that `#print axioms` applies.  Extreme inputs: `λ = 0` (`ouMat_ba_zero`, `UNEMCTE2k_ba_zero`, `UNJakk_ba_zero`, `UNUywk_ba_zero`, `BASelf_msc`), `t = 0` (`UNOUQUEk_zero_of_UNQuek`), `mean = 0` (`ouMat_band`).
### b.5 The drift and the sizes of the extra terms (scripts of (a) re-run; `drift.py`, `size.py`, `shift.py`)
```
$ python3 drift.py   (exact Wick, f = Tr H^4, d = 3, L = 3, W = 2, N = 216)
A. exact Wick, f = Tr H^4:  d/dt E f (central difference of closed form)  vs  generator RHS
   lam   flow        t     LHS             RHS(drift+gen)   drift term       RHS w/o drift    LHS-RHS
   0     non-centred 0.7  -1.66306266     -1.66306264      -0.00000000      -1.66306264      -2.09e-08
   0     centred     0.7  -1.66306266     -1.66306264      0.00000000       -1.66306264      -2.09e-08
   0.3   non-centred 0.7  -311.01019068   -311.01019064    -309.34712800    -1.66306264      -3.62e-08
   0.3   centred     0.7  -1.66306266     -1.66306264      0.00000000       -1.66306264      -2.09e-08
$ python3 drift.py mc 3000   (f = Im N^{-1} Tr G(z), z = 0.2+0.5i, t = 0.7)
B. Monte Carlo (M=3000 samples), f = Im N^{-1}Tr G(z), mean +- standard error
 lam=0.3  z=(0.2+0.5j) t=0.7
   non-centred: LHS +0.05481 +- 0.00009 | gen -0.00021 +- 0.00001 | drift +0.05484 +- 0.00003 | LHS-(gen+drift) +0.00019 +- 0.00010 | LHS-gen +0.05502 +- 0.00009
   centred    : LHS -0.00003 +- 0.00009 | gen(=RHS) -0.00018 +- 0.00000 | LHS-RHS +0.00015 +- 0.00009
$ python3 size.py | sed -n '2p;3p;5p'
c'=0.000555556 tau_U=1.26263e-05 (1/79200=1.26263e-05) t*=N^{-1+tau_U}=0.00462994 (1/N=0.00462963)  N^{-c'+C tau_U}(C=21)=0.99844
lam=0.3  E=0.2 eta=0.00463 | Im m=0.813 | sample (lam/2)|Im N^-1 Tr Psi G^2|: mean 1.346 max 7.212 | naive (lam/2)||Psi|| Im m/eta = 158.1 | x t*: sample 0.00623, naive 0.732
lam=10   E=0.2 eta=0.00463 | Im m=0.644 | sample (lam/2)|Im N^-1 Tr Psi G^2|: mean 0.06986 max 0.4417 | naive (lam/2)||Psi|| Im m/eta = 4170 | x t*: sample 0.000323, naive 19.3
$ python3 shift.py
c      dd     L  W   lam   N          c'        tau_U       t*=N^(-1+tU)  lamHat-lam   floor N^(-ts/4)  t*/floor    req N^(-c'+C tU)  naive(d lam Im m)
0.1667 0.100  4  32  0.3   2097152    5.556e-04 1.2626e-05  4.7692e-07    7.154e-08    9.4115e-01       5.067e-07   0.99578           0.745 
0.1667 0.100  4  32  10    2097152    5.556e-04 1.2626e-05  4.7692e-07    2.385e-06    9.4115e-01       5.067e-07   0.99578           16.800
0.1000 0.050  5  32  0.3   4096000    1.667e-04 3.7879e-06  2.4415e-07    3.662e-08    9.8115e-01       2.488e-07   0.99867           0.745 
0.1000 0.050  5  32  10    4096000    1.667e-04 3.7879e-06  2.4415e-07    1.221e-06    9.8115e-01       2.488e-07   0.99867           16.800
```
### b.6 Split table (sources, files, GUE-phase classes: portmap P.2, P.3; totals by `split_total.py`)
| id | files | statements | lo / central / hi lines | role | depends on |
|---|---|---|---|---|---|
| UN-01b | `Universality/Pins` (amend T2174), `OU` (3 lines), `Test/Axioms` | A1, A2, `UNKind`, `UN*k`, generic rows, `un_claimAll_of_rowsk` | 600 / 850 / 1100 | prover-hard | T2174, T2177 |
| BA-C1 | `BA/UNPins` | `UNKind.ba`, `UNMLOutBA`, `UNLocAvgBA`, `UNQueBA`, `BAEnd_QUEL`, BA rows, `PrecL`.., `ouMat_ba_eq_*`, `baBUniv_of_rows` | 700 / 950 / 1300 | prover-hard | BA-D1, UN-01b |
| BA-C2 | `BA/MReg` | regularity of `m(z, λ)` (`UNDensBARow`), the shift `m(z, λe^{t/2}) - m(z, λ)` | 800 / 1100 / 1600 | prover-max | BA-D2, D3, D4, D6, D7 |
| BA-C3 | `BA/GUEKPrim`, `BA/GUEEntry` | T declarations of `KPrim`, `ZeroModeProfile`, `EntryDet`, `EntryTail` (UN-29, 30, 41, 42, 51) | 788 / 1102 / 1575 | prover-max | BA-P8, K1, C1 |
| BA-C4 | `BA/GUEOneLoop` | T declarations of `OneLoop`, `Eq729A` (UN-44, 45, 46) | 620 / 868 / 1240 | prover-max | BA-K4, C3 |
| BA-C5 | `BA/GUEHyp` | T declarations of `Eq729B`, `HypA`, `Proc`, `PathBounds` (UN-31, 47, 48, 50) | 870 / 1217 / 1739 | prover-max | BA-T4, T5, C4 |
| BA-N1, BA-N2 (T2161 rows) | `BA/UNStep1`, `BA/UNBUniv` | grow by about 300 and 200 lines: BA instances of `UNTrLocal`, `UNTrLocalInit`, `UNNorm`; `BAGlueUniv` re-pinned | +300, +200 | prover-hard, prover | BA-D6, M1, C2; BA-N1, C5 |
```
W_T (lines, scaled to kept lines): T-class files 4277, T-bits in the other files 277, total 4554
total twin lines                                                                |  2278  3187  4554
tickets (greedy packing, cap 1500): {'lo': 2, 'cen': 3, 'hi': 5}
UN gate overhead of the model-generic design (parametrisation W_P x beta):  {'lo': 577, 'cen': 1154, 'hi': 1732} lines in the 28 GUE-phase tickets
BA total, model-generic UN design:  {'lo': 61, 'cen': 62, 'hi': 66}  (new BA tickets {'lo': 4, 'cen': 5, 'hi': 9} )
BA total, band-only UN design:      {'lo': 71, 'cen': 75, 'hi': 82}  (C1,C2 + full twin {'lo': 12, 'cen': 16, 'hi': 23} )
UN total with UN-01b: 52 + 1 = 53 (cap 60, DECISIONS 50)
```
GUE-phase classes (27 files, `declinv.py`, portmap P.2): T = KPrim ZeroModeProfile EntryDet EntryTail Eq729A Eq729B HypA OneLoop PathBounds Proc; P = AuxCarrier BoundsA Drift DuhamelB DuhamelC EntryGrid Generator HypB LLTransfer RandomLayerA RandomLayerB QUEFlow; G = Bootstrap BootstrapAt DuhamelA Grid Markov.
### b.7 Narrative
1. Verdict: targets 1-6 delivered.  The probe compiles (b.1): 149 theorems on the three standard axioms, no `sorry`; 25 blocks (2186 lines) of the T2162 and T2161 probes are copied verbatim and identical to the branch files; 28 named instances (b.4).  Not compiled: the generator identity (UN-15), the uniqueness-dependent bulk facts (d.6).
2. Target 1 (interface).  Every T2162 Claim pin is stated for `UNModel.band sz`, so none holds verbatim for `UNModel.ba`.  `UNKind` bundles the four data in which the classes differ (`M`, `lamV`, `bulk`, `mdet`).  `UNOUQUEk, UNOUDiagk, UNEMCTE2k, UNJakk, UNUywk` are the T2162 text with `UNModel.band sz ↦ K.M sz`, the profile coupling of `L1t, L2t, scirc` `sz.lam n ↦ K.lamV sz n` (EMCTE2, Jak, Uyw; BA: 0, `S^{(B)}(0) = I`) and `|E| ≤ 2-κ ↦ K.bulk sz κ E n` (OUQUE, OUDiag, the consumed `(Meq:QUE)` and `(G_bound_ave)`); at the band kind they are T2162's pins (b.3).  The QUE window (`lam`), `(ε₀, c) = (𝔡/3, 𝔡/6)`, `c' = 𝔠𝔡/30` and every exponent are unchanged; the BA bad event is a one-block event (`unBadYBA_subset`, `ℙ(𝓑) ≤ p`, no factor `2d+1`).  `un_claimAll_of_rowsBA` and `inst_claimAll_ba` give `UNClaimAll sz (UNModel.ba sz) E` from the BA rows.  The consumed `UNQueBA` is the first half of T2161's `BAEnd_QUE` with the law corrected (`UNQueBA_of_BAEnd_QUEL`); `UNLocAvgBA` against `BAEnd_locSC` is not bridged (BA-M1: `Prec` form against the explicit threshold).
3. Target 2 (drift).  For `H = V + λΨ` the matrix of T2162 has the mean `e^{-t/2}λΨ`, so `d/dt 𝔼Φ(𝐇_t) = -½e^{-t} Σ S°_{ab} 𝔼∂_{ab}∂_{ba}Φ - ½e^{-t/2} 𝔼 dΦ(𝐇_t)[λΨ]`; RBM2D `Universality/OUGenerator.lean:940` (c9a24cf) has only the first term (mean-zero carrier).  b.5: the exact Wick check of `Tr H⁴` and the Monte Carlo of `Im N⁻¹Tr G` reproduce both terms (LHS - RHS = -3.6e-8; the drift is -309.35 against -1.66, the dominant term); `drift_entry` compiles the matrix-level derivative `-½e^{-t/2}μ_{ij}`.  Its trivial bound `d λ Im m t*/η` is N-independent (0.745, 16.8) while (417) needs `N^{-c'+Cτ_U}` (`C = C_max = 21`, `τ_U = c'/44`, (a)), exponent `-23c'/44`: not an absorbable error (`drift_not_absorbable`).  Decision: the centred flow, drift 0, which is the paper's flow `(MBM)` (`1_2:686`, `H_0 = ilambda Ψ`; merged `seqHflowBA`).  It keeps `m(z, λ)` and the bulk set for every `t` (the free-convolution endpoint has `m' = m(z, λ)` to 8e-15, (a)); `ouMat (ba sz)` at `t_n` is the non-centred OU matrix of the model at `λ̂ = λ e^{t_n/2}` (`ouMat_ba_eq_ouMatNC`, same law `ouP`: `rfl`), admissible at `(𝔠, 𝔡/2)` (`admissible_lamHat`); the shift `λ̂ - λ` is 7e-8 (2.4e-6) and `t*/floor = 5e-7` (b.5).  The proof of `EMCTE2` (RBM2D `Universality/EMCTE2.lean:440,493`) changes in two places: the generator is stated for `Φ_μ(Y) = Φ(μ + Y)` (`TestFunH`) with the profile `svarF lamV` (`OUGenerator.lean:940`), and `L1t, L2t` (RBM2D `Universality/Pins.lean:94,100`) take `scirc` at the coupling `lamV` (`S°^V = svarF 0 - 1/N`).  Since `ouMat (ba sz) - λΨ = ouMat (band (sz.withLam 0))` (`ouMat_ba_eq_band_add`, same `ouP`), the Gaussian-carrier facts (`ouSample_law`, the generator, Hessian, contraction) are the band facts at `sz.withLam 0`.
4. Consequences.  A1/A2 amend the merged UN-01 (6 names, b.1a); `UNCoreC` has both `UNTrLocal` (a priori bound, `H`) and `UNTrLocalInit` (Step 1, `A = μ + e^{-t*/2}(H - μ)`); `UNStep1GoodC` reads `ouInit`.  `baBUniv_of_rows` assembles `BAEnd_BUnivL` from `UNCoreC` and the BA rows (analogue of T2162 `un_bUniv_of_rows`); it shows that T2161's `BAGlueUniv` lacks `BAEnd_QUE` and the flow outputs (T2173b).
5. Target 3 (GUE phase).  Class T (deterministic data `M`, `K~`, `Θ~`, mixture profile in the statements): 10 files, 11038 kept lines; class P (only the scalar spectral flow `spectralZ`, `lemT`, `lemE` or `K~` as a parameter): 12 files; class G (no model data): 5 files (lists above).  Once the model is a parameter nothing ports without a change: G needs the carrier (`mean`), P the parameter `m(E, lam)`, T a BA twin of the T declarations: `W_T = 4554` lines, 2278 / 3187 / 4554 at α = 0.5 / 0.7 / 1.0 = 2 / 3 / 5 tickets (BA-C3..C5, convention of T2161 b.9).  P.2 has one row per file.
6. Target 4.  The exponent table of (a)(i) closes unchanged (`τ_U`, `c'`, window, threshold); rows added: `ℙ(𝓑)` one block, `λ̂` admissible at `(𝔠, 𝔡/2)`, shift against the floor, drift (b.5, P.5); constants depend on `κ` as in (a) (D403).
7. Target 5.  BA-C1 (pins), BA-C2 (regularity of `m(z, λ)`, row `UNDensBARow`: not among T2161's pins), BA-C3..C5 (T declarations of the GUE phase); BA-N1, BA-N2 of T2161 grow (est. +300, +200 lines); UN-01b amends T2174 and repairs T2177; totals in the top line and b.6.
8. Findings outside the targets: T2173a (`seqGvar_ne_withLam_zero`: the coordinate variance between neighbouring blocks is positive under `sz.seqP`, zero under `(sz.withLam 0).seqP`), T2173b, T2173d (top notices).

## (c) Verified Mathlib names (script `names.lean`, `shorten.py`: `#check`, output shortened; `#check_failure` for the absent ones)
```
Complex.coe_smul : ∀ (x : ℝ) (y : E), ↑x • y = x • y
Complex.real_smul : ∀ , x • z = ↑x * z
Matrix.inv_eq_right_inv : ∀ , A * B = 1 → A⁻¹ = B
Matrix.nonsing_inv_eq_ringInverse : ∀ (A : Matrix n n α), A⁻¹ = Ring.inverse A
Matrix.trace_smul : ∀ (r : α) (A : Matrix n n R), (r • A).trace = r • A.trace
Matrix.trace_one : ∀ , Matrix.trace 1 = ↑(Fintype.card n)
Matrix.smul_mul : ∀ [IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α), a • M * N = a • (M * N)
eq_inv_of_mul_eq_one_left : ∀ , a * b = 1 → a = b⁻¹
HasDerivAt.ofReal_comp : ∀ , HasDerivAt f u z → HasDerivAt (fun y => ↑(f y)) (↑u) z
HasDerivAt.mul_const : ∀ , HasDerivAt c c' x → ∀ (d : 𝔸), HasDerivAt (fun y => c y * d) (c' * d) x
HasDerivAt.exp : ∀ , HasDerivAt f f' x → HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x
HasDerivAt.sub_const : ∀ (c : F), HasDerivAt f f' x → HasDerivAt (fun x => f x - c) f' x
HasDerivAt.div_const : ∀ , HasDerivAt c c' x → ∀ (d : 𝕜'), HasDerivAt (fun x => c x / d) (c' / d) x
hasDerivAt_id : ∀ (x : 𝕜), HasDerivAt id 1 x
tendsto_rpow_neg_atTop : ∀ , 0 < y → Filter.Tendsto (fun x => x ^ (-y)) Filter.atTop (nhds 0)
Real.rpow_le_rpow_of_exponent_le : ∀ , 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
Real.exp_one_lt_d9 : Real.exp 1 < 2.7182818286
Real.exp_le_exp : ∀ , Real.exp x ≤ Real.exp y ↔ x ≤ y
Real.one_le_exp : ∀ , 0 ≤ x → 1 ≤ Real.exp x
MeasureTheory.Measure.prod_prod : ∀ [MeasureTheory.SFinite ν] (s : Set α) (t : Set β), (μ.prod ν) (s ×ˢ t) = μ s * ν t
Equiv.apply_symm_apply : ∀ (e : α ≃ β) (x : β), e (e.symm x) = x
mul_left_cancel₀ : ∀ [IsLeftCancelMulZero M₀], a ≠ 0 → a * b = a * c → b = c
Complex.ofReal_ne_zero : ∀ , ↑z ≠ 0 ↔ z ≠ 0
le_mul_of_one_le_right : ∀ [PosMulMono α], 0 ≤ a → 1 ≤ b → a ≤ a * b
MeasureTheory.measure_mono : ∀ [MeasureTheory.OuterMeasureClass F α], s ⊆ t → μ s ≤ μ t
add_sub_cancel_left : ∀ (a b : G), a + b - a = b
Filter.Eventually.mono : ∀ , (∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
Unknown identifier `eq_inv_iff_mul_eq_one₀` | Unknown constant `Matrix.inv_one` | Unknown constant `Real.abs_sqrt_sub_sqrt_le`
```
Deprecated in this Mathlib (warning text of `lake env lean dep.lean`): `if_pos` -> `ite_eq_left`, `if_true` -> `ite_true`, `if_false` -> `ite_false`, `dif_pos` -> `dite_eq_left`.

## (d) Open issues and paper-delta candidates
1. BA count: 62 (61..66) ≤ 70 only if UN-25..52 are written model-generic (P.4); band-only 75 > 70 (top line).  UN-07 stays: the abstract Step 1 uses the Lipschitz clause of `UNDens`.
2. UN-01 is merged (T2174), and `OU.lean`, `EigenMeasurable.lean`, `GUEInvariance.lean` since (T2177, T2175): UN-01b amends `Universality/Pins.lean` (A1, A2, `UNKind`, generic pins and rows), repairs 3 lines of `OU.lean` (b.1a) and registers the new Props in `Test/Axioms.lean` (DECISIONS §16, §20; classes as in the probe docstrings: owed for the rows and pins, `UNKind` is data).  A ticket in flight that unfolds `ouMat` or builds a `UNModel` needs the same repair; at `a52eb85` only `Pins.lean`, `OU.lean`, `EigenMeasurable.lean` mention the amended names.  Alternative, not compiled: keep `UNModel` and `ouMat`, put `flow` and `init` into `UNKind`: no merged file changes, but `UNClaim417`, `UNApriori`, `UNGreenCorr`, `UNInfty1`, `UNUnivMain` (`Pins.lean:508-570`) get `UNKind` copies, and the lemmas over `UNModel` (`measurable_ouMat`, ...) do not apply to the BA flow.
3. Interfaces to freeze: the BA-V3 output `UNMLOutBA`; `UNLocAvgBA`, `UNQueBA` (BA-M1, M3: `∩_z` and the block inside the probability); T2161's end pins and carrier predicates over a law parameter (`PrecL`, `BAEnd_QUEL`, T2173a); `BAGlueUniv` re-pinned (T2173b).
4. New BA deterministic input (BA-C2): the uniform modulus of `(z, λ) ↦ m(z, λ)` on the bulk, uniform in `L` and `λ ∈ [W^{-d/2+𝔡}, 𝔡⁻¹]`; T2161's `BAoffDiag` (`:631`) is the stability constant on the real axis only, no T2161 pin has the modulus off the axis (derivation not compiled).
5. The classification of P.2 is from tokens and headers; each UN-25..52 preflight re-checks its file; the record `GUEDet` of deterministic data is fixed by the first T ticket (UN-29).
6. Not compiled: the generator identity with its drift (UN-15; b.5 is numerical); `BAm d L 0 = msc` and `BArho = rhoSC` at `λ = 0` (needs uniqueness; `BAmExists` has `0 < g`); the ρ-bulk at a prescribed coupling (T2161 open issue).  The route does not cover the non-centred flow (its drift is not absorbable, b.5); no input is proposed for it.
7. Paper-delta candidates: **T2173a** (law of the BA pins: `(sz.withLam 0).seqP`, not `sz.seqP`); **T2173b** (`BAGlueUniv` needs `BAEnd_QUE` and the BA-V3 outputs; the paper lists decol, locSC, QUE as inputs, `1_2:567-568`); **T2173c** (for BA the proof of Thm 2.4 runs on the centred flow `(MBM)`, `1_2:686`; the paper says "as in the band case", `7_8:1835`); **T2173d** (density regularity of `m` beyond `lem:propM`, `UNDens`); **T2173e** (`M_{y,α}` for BA has the weights `S^V = I`: one block; a reading of "defined below (2.24) of [DYYY25]", variant of T2162a).
