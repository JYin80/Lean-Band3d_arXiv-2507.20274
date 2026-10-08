Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 10:37:03 UTC 2026

Notation: `g = ilambda = sz.lam n`, `A = g² W^d` (`STAI`, Step34Pins:79), `ρ_u = (1-s)/(1-u)`, `N = sz.size n`, `𝒯_u(r) = B_{u,r} e^{-√(r/ℓ_u)}` (`tailT`), `r = |a₁-a₂|_∞`. Regime (i): `g²/L² ≤ 1-t ≤ 1-u ≤ 1-s ≤ g²` (`STReg5I`).

### (i) Exponent table and definition table

| Row | Value / declaration | Constraint it must satisfy | Slack |
|---|---|---|---|
| D1 | `𝓑 = STLKM sz n E s (seqHflow n s ω) σ b` (Step2Defs:68); kernel `𝒰_{s,u,σ} = RBM.Ind.Ugen` | `Ugen = Σ_b ∏_i((s/u)δ + ((u-s)/u)Θ_u)(a_i,b_i) X_b` (`step5Kernel_UN_decompU`, needs `0 < u`) | `u = 0` (then `s = u = 0`): `𝒰 = id`, treat separately |
| D2 | `𝒯̃^L_{u,D}` = `STprof` = `W^{-d}·tailW d L g u L W D r`; `f^{far}` = `STfFar` (Step5Pins:364), Θ at `ξ = u·m(σ₁)m(σ₂) = u` for `σ₁≠σ₂` (`‖m‖=1`); `f^{near}`, `g_a` have no Lean def (new, file-private) | `f + g = (1-s)²(Θ𝓑Θ)_a` is an algebraic identity (`Σ_{b₂}𝓑_{b₁b₂}` by Ward, `B45_ward_fin`, alternating σ) | exact |
| D3 | `Θ` symmetric: `Theta_transpose_of_three_le` (Props4:95) | `Θ_{a₂b₁} = Θ_{b₁a₂}` in `g_a` | exact |
| 1 | target exponent `1/5` (`A^{-1/5}W^{-d}𝒯̃`) | `STDecay` at `s` gives `Bctl(s)^{1/5} ≤ ((1+2^{d-1})/A)^{1/5}` (zero-mode term, `g²/L² ≤ 1-s`, `zeroMode_le_of_ge`) | 0 in the exponent (equality); constant absorbed by `≺` since `A^{-1/5} ≥ N^{-b}` |
| 2 | shape `6/5 = 1/5 + 1`: `A^{-6/5}/(r^{d-2}+1)` ≲ `N^τ A^{-1/5}W^{-d}𝒯_u(r)` | `B_{u,r} ≥ (g²+1-u)^{-1}(r+1)^{-(d-2)} ≥ (2g²)^{-1}2^{-(d-2)}(r^{d-2}+1)^{-1}` (uses `1-u ≤ g²`), `e^{-√(r/ℓ_u)} ≥ e^{-(log W)^{3/4}} ≥ W^{-τ}` in window `r ≤ (log W)^{3/2}ℓ_u` | any `τ > 0` |
| 3 | `𝔠_d ∈ (0, 1/100]` := the constant of `stCltFar_holds` (one `∃𝔠d` before `s,t`, so one `𝔠_d` serves every `t'`) | `ρ_u ≤ ρ_t ≤ Bctl(t)^{-𝔠_d} ≤ (2A)^{𝔠_d}`; `Bctl(t) ≥ W^{-d}(g²+1-t)^{-1} ≥ 1/(2A)` (uses `1-t ≤ g²`) | `𝔠_d ≤ 1/100` |
| 4 | closure of the last `≤` of `(eq:boundga)` (see (ii)) | `(1+2^{d-1}) 2^{𝔠_d} A^{-(4/5-𝔠_d)} ≤ 1` | exponent `4/5-1/100 = 79/100`; needs `A ≥ W^{2𝔡}` (`lam_sq_mul_pow_ge`) and `W ≥ W_*(d,𝔡)` (script C: `W_* = 2.77e4` (d=3,𝔡=.1), `6.4e7` (d=5,𝔡=.1)) |
| 5 | `f^{near}`: `(1-s)² g^{-4} ℓ_s⁴` | `ℓ_s² = g²/(1-s)` exactly in (i) (`g/√(1-s) ≥ 1` as `1-s ≤ g²`; `≤ L` as `1-s ≥ g²/L²`) | `= 1` exactly (not `≲ 1`); polylog `(log W)^{14}` from `R = (log W)³ℓ_s`, `R' = (log W)⁴ℓ_s`, `R²R'²/ℓ_s⁴`; `≺` absorbs |
| 6 | split `ρ_u ≶ (log W)^{10}` | `ρ_u ≤ (log W)^{10}`: kernel loss `ρ_u`, floor loss `ρ_u²` (≤ `(log W)^{20}`, absorbed); `ρ_u > (log W)^{10}` ⇒ `ℓ_u = √ρ_u ℓ_s > ℓ_s (log W)^5` (equality `ℓ_u/ℓ_s = √ρ_u` in (i)) | exact; `STCltFarConcl` index set ⊇ the (σ,a) at which the CLT is used |
| 7 | window `(4)` | `r ≤ ½(log W)^{3/2}ℓ_u + (log W)^{5/2}ℓ_s ≤ (log W)^{3/2}ℓ_u` when `ℓ_u ≥ ℓ_s(log W)^5` | `ℓ_s(log W)^4 ≥ 2` |
| 8 | floors `W^{-D'}` | `N^C ≤ W^{C/𝔠}` (`Bandwidth 𝔠`, `𝔠 > 0` in `Admissible`): `D' = D + C/𝔠 + 1` | free |
| 9 | grid for `u`-uniformity: `δ_n = N^{-12}`, `K_n ≤ N^{12}+1` points | `|f(u)-f(u')| ≤ 4(1-s)²L^{2d}N^τ δ (1-t)^{-3}` with `(1-t)^{-1} ≤ L²g^{-2} ≤ L²W^d`; floor of control `A^{-6/5}/(L^{d-2}+1) ≥ N^{-b}` | script v: error `≤ 1e-20 ×` floor in all rows; union `D'' = D + 13` |
| 10 | profile lemma hypotheses `(u,t) ↦ (s,u)` | `0 ≤ s ≤ u < 1`, `g²/L² ≤ 1-u ∨ 1-s ≤ g²/L²` (`step5Kernel_profile_explicit_holds`; `ekPropTInf_holds` at `(u,u)`: `g²/L² ≤ 1-u`) | `1-u-g²/L² ≥ 0` from `STReg5I` at `t ≥ u` |
| 11 | zero-mode constant `1+2^{d-1}` (`zeroMode_le_of_ge`, `r ≤ L`, `g²/L² ≤ 1-·`) | `B_{·,r} ≤ (1+2^{d-1})(g²+1-·)^{-1}(r+1)^{-(d-2)}` | script B: max ratio 1.0879 ≤ 5 at `d=3` |
| 12 | `(u-s)/u ≤ 1-s` (`us ≤ s`) | mixed terms `(1-s)Σ_b|Θ_u|𝒯̃_s ≤ C𝒯_u + ρ_u W^{-D}` (profile lemma with tail time `s`, kernel time `u`, factor `1-s`): no `ρ_u` in the main term | exact |

### (ii) Steps (1)-(7) against `3_5:2077-2172`, and one concrete instance

**(1) `σ₁=σ₂`.** `Θ^{(σ,σ)}` has `|Θ_{ab}| ≤ C_s(δ_{ab} + g²e^{-c₀|b-a|})` (`prop5Short_holds`, `κ ≤ Im m`). In `IniTermII` the regime `hreg: 1-s ≤ g²/L²` reaches the `σ₁=σ₂` path only through `iniTermII_Ts_le` (:1110, used :1316; grep `hreg`), i.e. `ℓ_u = L` (`e⁻¹B_{u,r} ≤ 𝒯_u(r)`). In (i) `ℓ_u < L`; replace it by: `B_{s,r'} ≤ (1+2^{d-1})(r'+1)^{-(d-2)}(g²+1-s)^{-1} ≤ (1+2^{d-1})(m+1)^{d-2}B_{u,r}` (row 11, `r ≤ r'+m`, `m = |b₁-a₁|+|b₂-a₂|`) and `e^{-√(r'/ℓ_s)} ≤ e^{-√(r/ℓ_u)}e^{√m}` (`√(r/ℓ_u) ≤ √(r'/ℓ_u)+√m`, `ℓ_u ≥ ℓ_s ≥ 1`); `Σ_x(x+1)^{d-2}e^{√x}e^{-c₀x} < ∞`, no `Σ_x 1 ≲ L²`. So `𝒯_s(r') ≤ (1+2^{d-1})(m+1)^{d-2}e^{√m}𝒯_u(r)` (script B: 205 triples, max constant 0.83). Not a pure "exponential row sum" replacement: the `e^{√m}` shift is needed.
**(2) `σ₁≠σ₂`.** Four terms of `(eq:decompU)`: `(s/u)²𝓑` (`𝒯_s ≤ 𝒯_u`, script B), two mixed terms (row 12, `STDecay` at `s`), and `(u-s)²/u² · (Θ𝓑Θ)`, with `(u-s)²/u² ≤ (1-s)²`. `u=0`/`s=u`: row D1.
**(3) `ρ_u ≤ (log W)^{10}`.** Two profile-lemma applications, main factor `ρ_u` (second application has `1-s = ρ_u(1-u)`), floor `ρ_u²W^{-D'}`; no CLT. The ticket's `ρ_u²` multiplies only the floor.
**(4) Regime reduction.** If `ρ_u > (log W)^{10}`: outside `r ≤ ½(log W)^{3/2}ℓ_u + (log W)^{5/2}ℓ_s` one of `|a₁-b₁|`, `|b₂-a₂|` ≥ `¼(log W)^{3/2}ℓ_u` or `|b₁-b₂| ≥ (log W)^{5/2}ℓ_s`. The first two need `e^{-c|x|/ℓ_u}` of `prop5Decay_holds` (Prop5Hold:784); `step5Kernel_theta_decay` gives only `e^{-√(x/ℓ_u)}`, `e^{-½(log W)^{3/4}}`, which is NOT `≤ W^{-D}`. The third uses `STDecay`'s `e^{-√(y/ℓ_s)} ≤ e^{-(log W)^{5/4}}`. Inside: `e^{(log W)^{3/4}} ≤ W^τ` (row 2).
**(5) `g_a`.** `Σ_{b₂}𝓑 = Im(𝓛-𝒦)^{(1)}_{s,+,b₁}/(W^dη_s)` (`B45_ward_fin`, both signs for `σ=(+,-),(-,+)`), `η_s = (1-s)Im m ≥ (1-s)κ_m` (`etaT`, `iniTermII_im_ge`), `STAvgU` at `u = s` (index `⟨s,_⟩ ∈ TimeIcc s t`), `Bctl(s) ≤ (1+2^{d-1})/A`, `|Θ_{ab}| ≤ C𝒯_u(|b-a|)` (`step5Kernel_theta_decay`), `Σ_b𝒯_u𝒯_u ≤ C(1-u)^{-1}𝒯_u` (`ekPropTInf_holds`, `g²/L² ≤ 1-u`):
`|g_a| ≤ N^τ C ρ_u A^{-1}W^{-d}𝒯_u(r)`. **Exact inequality behind the last `≤` of `(eq:boundga)`:** `W^{-d}𝒯_u(r) ≤ (1+2^{d-1})A^{-1}/(r^{d-2}+1)` (rows 11, `(r+1)^{d-2} ≥ r^{d-2}+1`, `(g²+1-u)^{-1} ≤ g^{-2}`), hence `ρ_u A^{-1}W^{-d}𝒯_u(r) ≤ A^{-6/5}/(r^{d-2}+1) · [(1+2^{d-1})ρ_u A^{-4/5}]` and `[…] ≤ (1+2^{d-1})2^{𝔠_d}A^{-79/100} ≤ 1` eventually (row 4); it is an inequality for `A ≥ A_*`, not an identity.
**(6) `f^{near}`.** `|𝓑_{b₁b₂}| ≤ N^τ A^{-6/5}(|b₁-b₂|^{d-2}+1)^{-1}` from `STDecay` at `s` (row 1, `W^{-d}B_{s,y} ≤ (1+2^{d-1})A^{-1}(y+1)^{-(d-2)}`) and `≤ W^{-D}` for `|b₁-b₂| ≥ (log W)³ℓ_s`; `|Θ_u(x)| ≤ C g^{-2}(|x|+1)^{-(d-2)}` (`prop5Decay_holds`, row 11). Sums: `Σ_{|y|≤R}(|y|+1)^{-(d-2)} ≲ R²`; `Σ_{|x|≤R'}(|x|+1)^{-(d-2)}(|x-w|+1)^{-(d-2)} ≲ R'²(|w|+1)^{-(d-2)}` up to a `log` for `d=4` (checked by hand: `d=3` gives `R'` vs `R'²/(|w|+1)`; `d ≥ 5` gives `(|w|+1)^{-(d-4)} ≲ R'²(|w|+1)^{-(d-2)}` for `|w| ≲ R'`; `|w| ≥ 2R'`: `≲ R'²(|w|+1)^{-(d-2)}`), via `Defs/RadialSum`, `Defs/Convolution`. Total `≲ (1-s)²g^{-4}·A^{-6/5}·R²R'²/(r^{d-2}+1)`; the last constant is `(1-s)²g^{-4}ℓ_s⁴ = 1` exactly (row 5).
**(7) `f^{far}` and `u`-uniformity.** `STfFar` filter uses `ℓ_s` only; `t` enters only through `Θ_ξ`, `ξ = u`. The merged `STCltFarConcl` index set at time `t'`: `σ₀≠σ₁`, `(log W)^5 ℓ_s ≤ ℓ_{t'}`, `r ≤ ½(log W)^{3/2}ℓ_{t'} + (log W)^{5/2}ℓ_s`, controls `A^{-6/5}/(r^{d-2}+1)`. For `u ≤ u_k`: `ℓ_u ≤ ℓ_{u_k}` (`ellT_mono`, Kernel/PropT:58), so every `(σ,a)` with `ρ_u > (log W)^{10}` that is relevant at `u` lies in the index set at `u_k`. Resolvent identity `Theta_sub_Theta` (Propagator/Deriv:57): `|Θ_u-Θ_{u'}|_{ab} ≤ |u-u'|(1-u)^{-1}(1-u')^{-1}` (row sums `sum_norm_Theta_row_le`, Props4:210). **No deterministic `‖𝓑‖ ≤ N^C` is needed or claimed:** w.h.p. `|𝓑| ≤ N^τ` from `STLK` (`k=2`) at `s` (`Bctl(s) ≤ 1` eventually) and the high-probability absorption `StochDomAt.of_highProbAt_add_rpow_neg` (StochDomAt:697, lower bound `N^{-b}`); union over the grid by `Path.highProbAt_iInter` (`≤ N^{12}+1` points). Per grid point apply `stCltFar_holds` to the worst sequence `t'_n = u_{n,k*_n}` (`k*_n` maximises the failure probability, `Finset.exists_max_image`), `s_n < t'_n ≤ t_n`, `u_{n,k} = min(s_n+kδ_n, t_n)`, `k ≥ 1` (`u = s` has `ρ = 1`: branch (3)).

**Instance.** (A) Sequence data of the merged `inst_iniTermI` (Step5Pins:617): `szB` (`d=3, L=4, ilambda=1, W_n = n+4`), `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z_n = 1/2 + i/64`, `s=7/8`, `t=15/16`, `t' = 29/32`. (B) Deterministic cores: `d=3, L=8, g=1/2, E=1, W=2, D=2, s=7/8, u=15/16, M=λ=1`, `X_b = λW^{-d}𝒯_s(|b₁-b₂|)+W^{-D}` (min over `b` 0.263 > 0). (C) CLT data `szCL` (`s=0`, `1-t = L^{-2}`, `L = 2m^5`, `W = 2^m`, `m = n+24`; merged `szCL_cltFar_index_nonempty`). External hypothesis `(eq:WO)`/`Bandwidth`: limit computations in script A, D.

```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2329/pre.py   # exit 0
A szB n=0 N=4096 W=4 regI/WO/Band/loc/locIm/t<=lemT: True
A szB n=10 N=175616 W=14 regI/WO/Band/loc/locIm/t<=lemT: True
A szB n=1000 N=64771076096 W=1004 regI/WO/Band/loc/locIm/t<=lemT: True
A lemT(zB)=0.983992 >= t=0.937500; ell_s=2.8284 ell_t=4.0000 rho_t=2.000
B hypotheses (L>=3,g>0,|E|<=2,kappa_m=1/2<=Im m=0.8660,0<=s<=u<1,1-s<=g^2,g^2/L^2<=1-u): [True, True, True, True, True, True, True]
B ell_s=1.41421 ell_u=2.00000 ell_u/ell_s=1.41421 sqrt(rho)=1.41421; (1-s)^2 g^-4 ell_s^4=1.000000000000
B max B_{.,r}/[(g^2+1-.)^-1 (r+1)^-(d-2)] over r<=L: 1.0879 <= 1+2^(d-1)=5
B tail comparison T_s(r')<=C (m+1)^(d-2) e^sqrt(m) T_u(r), r<=r'+m: 205 triples, max C=0.8301 <= 5
B T_s<=T_u for r<=L: True
B X_b profile (nonzero) min=0.26277
C closure (1+2^(d-1)) 2^cd A^-(4/5-cd) <= 1 at worst A=W^(2dd) (lam^2=W^(-d+2dd)):   [value must be <= 1]
 d=3 dd=0.05 margin(W=1e2,1e5,1e8)= ['3.5', '2.03', '1.17']  threshold W_*=7.69e+08
 d=3 dd=0.10 margin(W=1e2,1e5,1e8)= ['2.43', '0.817', '0.274']  threshold W_*=2.77e+04
 d=4 dd=0.05 margin(W=1e2,1e5,1e8)= ['6.3', '3.65', '2.11']  threshold W_*=1.31e+12
 d=4 dd=0.10 margin(W=1e2,1e5,1e8)= ['4.38', '1.47', '0.493']  threshold W_*=1.14e+06
 d=5 dd=0.05 margin(W=1e2,1e5,1e8)= ['11.9', '6.89', '3.99']  threshold W_*=4.11e+15
 d=5 dd=0.10 margin(W=1e2,1e5,1e8)= ['8.27', '2.78', '0.932']  threshold W_*=6.41e+07
C regime-(i) grid points=2520 violations of [ell_s^2=g^2/(1-s), ell_t/ell_s=sqrt(rho), (1-s)^2 g^-4 ell_s^4=1]=0
C window check log^2.5*ls<=0.5*log^1.5*lu for lu=ls*log^5, ls=1,log W in [2,20]: True
v d=3 W=1e+02 L=8: log10 N=8.7, log10 grid error=-75.1, log10 control floor>=-21.6, ok=True
v d=3 W=1e+06 L=100: log10 N=24.0, log10 grid error=-209.4, log10 control floor>=-55.2, ok=True
v d=5 W=1e+08 L=1000: log10 N=55.0, log10 grid error=-491.4, log10 control floor>=-123.4, ok=True
D szB con_st_ind(cd=1/100) t=15/16: (1-t)/(1-s)=0.500, holds for all W>=11984934085 (monotone in W); s<t'<=t and Bctl(t')<=Bctl(t): True
D szB con_st_ind(cd=1/100) t'=29/32: (1-t)/(1-s)=0.750, holds for all W>=15407 (monotone in W); s<t'<=t and Bctl(t')<=Bctl(t): True
D szCL m=24: L=15925248 W=16777216 W>=L:True regI: g^2/L^2=1-t<=1-s=1<=g^2: True; log^5 W=1.27e+06 <= ell_t=L: True (index nonempty)
D szCL con_st_ind(cd=1/100) holds for all m>=4063 (W=2^m): eventual in n, not at m=24 (n=0)
ALL OK
```

### (iii) DECISIONS §29 checks (one line each)
- Regime `STReg5I` (§29 (1),(2),(4)): `∀ n`; `0 ≤ s`, `t ≤ lemT < 1` are premises; `1-t ≥ g²/L²` with `g > L` is empty (no `n`), no negative-time boundary arises; `ConStInd` is `∀ᶠ n` and restricts to `t'` (row 3, script D: threshold for `t'` 15407 < threshold for `t`).
- `𝔠_d`: the `∃𝔠d ∈ (0,1/100]` of `stCltFar_holds` (CltFar:1757), taken before `s, t`; closure exponent `79/100` (row 4).
- `(log W)^{10}` split (row 6): scale `(log W)^k ℓ_s` as in `STfFar`/`STCltFarConcl`, not `W^τ ℓ`; §29 (3): only `N ≥ L^d`-type counts (`N=(WL)^d`), `W ≥ N^𝔠` for floors, no `L^d ≤ W^K`. §29 (5): `Prec` (union inside `P`); (6): `g ≥ W^{-d/2+𝔡}`, `A ≥ W^{2𝔡}`, `W→∞` from `Admissible`; the ticket's "`ilambda² ∈ [W^{-d/2+𝔡}, 1]`" is not the merged `WO`: `W^{-d/2+𝔡} ≤ ilambda ≤ 𝔡^{-1}` (Sizes:163), so `g² ∈ [W^{-d+2𝔡}, 𝔡^{-2}]`; `g² > 1` is covered (`1-s ≤ 1 < g²`, `ℓ_s = g/√(1-s)` still).

### (v) `u`-uniformity route (7)(a)-(d)
(a) `STfFar` at time `u` depends on `u` only through `Θ_ξ`; Lipschitz bound by `Theta_sub_Theta` and `sum_norm_Theta_row_le` (row 9). (b) Index set grows with `ℓ_t` (`ellT_mono`). (c) argmax sequence `t'_n` and union (above). (d) Every hypothesis of `STIngR5` at `(s,t')` for `s < t' ≤ t` (`stIngR5_hyps_restrict`):
`0 ≤ s`, `s < t'` (grid `k ≥ 1`), `t' ≤ t ≤ lemT`; `STReg5I`: `1-t' ≥ 1-t`; `STKbound`, `STKward`, `STLK s`, `STDecay s`, `STDecayStrong s`: no `t`; `STConStInd 𝔠_d s t'`: `Bctl(t') ≤ Bctl(t)` (`STBctl_mono`, `t < 1`), `x ↦ x^{𝔠_d}` monotone (`𝔠_d > 0`), `(1-t)/(1-s) ≤ (1-t')/(1-s)`, `(1-t')/(1-s) < 1` iff `s < t'`; `STStep1Loop`, `STStep2Concl` (`STLocalEntryU`, `STAvgU`, `STGdecayW`), `STLmaxU`, `STLKU`: each `Prec` has index `TimeIcc s t n × …` and `ξ, ζ` that contain `s n` and `p.1` only (Step34Pins:176-216, Defs:234), so `StochDomAt.precomp_param` (StochDomAt:335) with `φ ⟨u,h⟩ = ⟨u, h.1, h.2.trans (t' ≤ t)⟩` gives them. No hypothesis fails.

## Verdicts
- `stIniTermI_holds`: PASS (route (1)-(7) closes; replace the case-(ii) tail comparison by the `e^{√m}`-shifted one in (1); (4) needs `prop5Decay_holds`, not `step5Kernel_theta_decay`).
- `iniTermI_core_same`: PASS (regime `g²/L² ≤ 1-u`, `1-s ≤ g²`; row 11).
- `iniTermI_core_mixed`: PASS as `ρ`-lossy bound `[𝒰X]_a ≲ ρ_u(…𝒯_u…) + ρ_u²W^{-D}` (branch (3)) plus the deterministic parts `g_a`, `f^{near}` and the exact identity `(1-s)²(Θ𝓑Θ) = f^{near}+f^{far}+g`; `f^{far}` itself is random (`STfFar`).
- `stIngR5_hyps_restrict`: PASS (every hypothesis restricts, listed in (v)(d)).
- `stCltFar_uniform`: PASS (route (v)(a)-(c); high-probability form, no deterministic `‖𝓑‖` bound).

## (a′) Preflight corrections — Thu Oct  8 12:26:26 UTC 2026
- Row 9 of (a) states the grid `δ_n = N^{-12}`; implemented: `M_n = N^{14}` points, spacing `≤ N^{-14}` (`iniTermI_unif_det`: error `≤ 16 N^{-5} ≤ N^{-3} ≤ ζ`). No verdict changes.
- The `iniTermI_core_mixed` verdict of (a) describes a `ρ`-lossy bound. In Lean the `ρ`-lossy bound is `iniTermI_core_lossy`; `iniTermI_core_mixed` is the exact
  `(eq:decompU)` split `𝒰X = U₀ + c (1-s)²(Θ𝓑Θ)`, `c = ((u-s)/(u(1-s)))² ∈ [0,1]`, `|U₀| ≤ C M (q 𝒯_u + ρ F)`; `f^{near}/g/f^{far}` are `iniTermI_mixed_bound`.

## (b) Script output

```
$ lake build RBM3D.Induction.IniTermI 2>&1 | tail -1
Build completed successfully (3826 jobs).
$ git diff --stat main...t/T2329          # branch t/T2329, commit 906f8a9 (git log -1 --format=%cd: Thu Oct 8 05:25:18 2026 -0700)
 RBM3D/Induction/IniTermI.lean | 3823 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    1 -
$ lake env lean ax.lean   # #print axioms of the targets and of the instances (names abbreviated: RBM.Gauss. omitted)
'Sizes.stIniTermI_holds' -> [propext, Classical.choice, Quot.sound]
'Sizes.iniTermI_core_same' -> [propext, Classical.choice, Quot.sound]
'Sizes.iniTermI_core_mixed' -> [propext, Classical.choice, Quot.sound]
'Sizes.stIngR5_hyps_restrict' -> [propext, Classical.choice, Quot.sound]
'Sizes.stCltFar_uniform' -> [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_iniTermI_proved' -> [propext, Classical.choice, Quot.sound]
'Step5Inst.iniTermI_core_same_inst' -> [propext, Classical.choice, Quot.sound]
'Step5Inst.iniTermI_core_mixed_inst' -> [propext, Classical.choice, Quot.sound]
'Step5Inst.iniTermI_restrict_inst' -> [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_cltFarU_proved' -> [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_cltFarU_CL' -> [propext, Classical.choice, Quot.sound]
'Step5Inst.iniTermI_cltFarU_index_nonempty' -> [propext, Classical.choice, Quot.sound]
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/IniTermI.lean
0
```

Targets, statements extracted by script (`python3 -I extract.py <name>`; file lines of `RBM3D/Induction/IniTermI.lean`):
```
3715: theorem stIniTermI_holds (d : ℕ) : STIniTermI d := by
1229: theorem iniTermI_core_same (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
1230:     ∃ C : ℝ, 0 < C ∧
1231:       ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
1232:         |E| ≤ 2 → κm ≤ (mE E).im → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam →
1233:         ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
1234:           (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
1235:           ∀ a, ‖RBM.Ind.Ugen d L g E σ s u X a‖ ≤
1236:             C * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + W ^ (-D)) := by
1143: theorem iniTermI_core_mixed (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
1144:     ∃ C : ℝ, 0 < C ∧
1145:       ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
1146:         |E| ≤ 2 → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam →
1147:         ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
1148:           (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
1149:           ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ a, ‖RBM.Ind.Ugen d L g E σ s u X a - (c : ℂ) * iniTermI_Sfull d L g s u X a‖ ≤
1150:             C * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) +
1151:               (1 - s) / (1 - u) * W ^ (-D)) := by
1577: theorem stIngR5_hyps_restrict {E s t t' : ℕ → ℝ} {𝔠d Cd : ℝ} (h𝔠d : 0 < 𝔠d)
1578:     (hst' : ∀ n, s n < t' n) (ht' : ∀ n, t' n ≤ t n) (ht1 : ∀ n, t n < 1)
1579:     (hR : STReg5I sz s t) (hCon : STConStInd sz 𝔠d s t) (hS1 : STStep1Loop sz E s t)
1580:     (hS2 : STStep2Concl sz E s t Cd) (hLmax : STLmaxU sz E s t) (hLKU : STLKU sz E s t) :
1581:     STReg5I sz s t' ∧ STConStInd sz 𝔠d s t' ∧ STStep1Loop sz E s t' ∧ STStep2Concl sz E s t' Cd ∧
1582:       STLmaxU sz E s t' ∧ STLKU sz E s t' := by
2005: theorem stCltFar_uniform (d : ℕ) : STIngR5 d STReg5I (fun sz E s t => STCltFarUConcl sz E s t) := by
1786: def STCltFarUConcl (E s t : ℕ → ℝ) : Prop :=
1787:   Prec sz (U := fun n => Σ u : TimeIcc s t n, STCltFarIdx sz s n (u : ℝ))
1788:     (fun n q ω => ‖STfFar sz n (E n) (s n) (q.1 : ℝ) q.2.1.1.1 q.2.1.2 ω‖)
1789:     (fun n q _ => STCltFarZeta sz n q.2.1.2)
```
`STIniTermI` is the merged pin (`Step5Pins.lean:322`); the check-file equality below shows `stIniTermI_holds : ∀ d, STIniTermI d` verbatim.

Compiled nonempty instances (same file, namespace `RBM.Gauss.Step5Inst`; all deterministic hypotheses discharged; `iniTermI_restrict_inst` keeps the four
`Prec` premises of Steps 1-4 as hypotheses (other gates' pins); `inst_*` have the `InstIng5Concl` shape of `Step5Pins.lean:539`, whose Step 1-4 premises are the
antecedent):
```
3819: theorem inst_iniTermI_proved (Cd : ℝ) (hCd : 0 < Cd) :
3820:     InstIng5Concl (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
3800: theorem inst_cltFarU_proved (Cd : ℝ) (hCd : 0 < Cd) :
3801:     InstIng5Concl (fun sz E s t => STCltFarUConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
3806: theorem inst_cltFarU_CL (Cd : ℝ) (hCd : 0 < Cd) :
3807:     InstIng5Concl (fun sz E s t => STCltFarUConcl sz E s t) szCL zCL sCL tCL Cd :=
3813: theorem iniTermI_cltFarU_index_nonempty (n : ℕ) :
3814:     Nonempty (Σ u : RBM.Path.TimeIcc sCL tCL n, STCltFarIdx szCL sCL n (u : ℝ)) := by
3786: theorem iniTermI_restrict_inst (Cd : ℝ)
3787:     (hS1 : STStep1Loop szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
3788:     (hS2 : STStep2Concl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) Cd)
3789:     (hLmax : STLmaxU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
3790:     (hLKU : STLKU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
3791:     STReg5I szB (fun _ => 7 / 8) (fun _ => 29 / 32) ∧ STConStInd szB (1 / 100) (fun _ => 7 / 8) (fun _ => 29 / 32) ∧
3792:       STStep1Loop szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 29 / 32) ∧
3793:       STStep2Concl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 29 / 32) Cd ∧
3794:       STLmaxU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 29 / 32) ∧ STLKU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 29 / 32) :=
3756: theorem iniTermI_core_same_inst : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 8,
3757:     ‖RBM.Ind.Ugen 3 8 (1 / 2) 1 ![true, true] (7 / 8) (15 / 16)
3758:       (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (7 / 8) (zdistInf 3 8 (b 0 - b 1) : ℕ)
3759:         + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)) a‖ ≤
3760:       C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (15 / 16) (zdistInf 3 8 (a 0 - a 1) : ℕ) +
3761:         (2 : ℝ) ^ (-(2 : ℝ))) := by
3769: theorem iniTermI_core_mixed_inst : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ a : Fin 2 → Zd 3 8,
3770:     ‖RBM.Ind.Ugen 3 8 (1 / 2) 1 ![true, false] (7 / 8) (15 / 16)
3771:       (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (7 / 8) (zdistInf 3 8 (b 0 - b 1) : ℕ)
3772:         + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)) a -
3773:       (c : ℂ) * iniTermI_Sfull 3 8 (1 / 2) (7 / 8) (15 / 16)
3774:         (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (7 / 8) (zdistInf 3 8 (b 0 - b 1) : ℕ)
3775:           + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)) a‖ ≤
3776:       C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (15 / 16) (zdistInf 3 8 (a 0 - a 1) : ℕ) +
3777:         (1 - 7 / 8) / (1 - 15 / 16) * (2 : ℝ) ^ (-(2 : ℝ))) := by
```
Data of the cores: `d = 3`, `L = 8`, `g = 1/2` (`1-s = 1/8 ≤ g² = 1/4`, `g²/L² = 1/256 ≤ 1-u = 1/16`), `W = 2`, `D = 2`, `E = 1`, `s = 7/8`, `u = 15/16`,
`M = λ = 1`, `X_b = W^{-d} 𝒯_s(|b₁-b₂|) + W^{-D} ≥ 1/4`.  `STCltFarUConcl`'s index set at `szCL` (`L_n → ∞`) is nonempty (`iniTermI_cltFarU_index_nonempty`).

Name-clash grep (all 121 declared names of the file, `grep -rlw` over `RBM3D/` outside `Probe/` and the file itself):
```
clashing names: 0
```
Ports: no text from `../RBM1D` or `../RBM2D` (`grep -c "RBM1D\|RBM2D" RBM3D/Induction/IniTermI.lean` = 0); the copied helpers come from this repo's `Induction/IniTermII.lean`
(private `iniTermII_*` ↦ `iniTermI_*`: lattice basics, `Kf`, `ZA`, `Ugen_rep`, `cyc_mixed`, `Theta_shift`, `poly_exp`, `bil_same` (re-derived with the `e^{√m}` weight),
`stageA` (regime hypothesis `g²/L² ≤ 1-u`), `Bctl_le`, `lam_le`, `prem_eq`, `prof_ge`, `im_ge`).  No `RBM1D`/`RBM2D` `git diff --stat` is applicable.

Acceptance checks (temporary uncommitted `import RBM3D.Induction.IniTermI` added to `RBM3D.lean` for the run, then removed; the hub adds it at merge):
```
$ lake build            # Thu Oct  8 12:23:27 UTC 2026 .. Thu Oct  8 12:24:13 UTC 2026, full build exit 0
info: RBM3D.lean:372:0: axiom audit: 10021 theorems, 2989 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4138 jobs).
$ printf 'import RBM3D\nimport RBM3D.Induction.IniTermI\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean   # exit 0
axiom audit: 10021 theorems, 2989 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 143 (borrowed 1, owed 84, structural 40, refuted 6, superseded 12).
registry: 2 borrowed + 135 owed + 105 structural + 7 refuted + 13 superseded; 119 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ lake env lean checkeq.lean  # = the check file's imports + `import RBM3D.Induction.IniTermI` + the check's `T2329_stIniTermI_holds` +
                              #   example : RBM.Gauss.Sizes.T2329Check.T2329_stIniTermI_holds := RBM.Gauss.Sizes.stIniTermI_holds   -> exit 0
```
Without the temporary root import the full `lake build` fails at `RBM3D.lean:371` with `premise(s) that no theorem proves ... [RBM.Gauss.Sizes.STIniTermI]` (the registry line is
deleted, no imported module proves it); this is the state the hub's merge step fixes.  A first run with the import failed on `RBM.Gauss.Sizes.STCltFarUConcl` (a Prop-valued def
assumed as a hypothesis by `iniTermI_concl` and concluded by no theorem); fixed by stating that hypothesis as the unfolded `sz.Prec ...` (`STCltFarUConcl` is then only a
conclusion-side name of `stCltFar_uniform`).

File map (`^/-! ###` headings, selected; the numbering of §1-§12 is that of the copied sections of `IniTermII.lean`):
```
52 1. Lattice sums for the power kernels
439 7. The kernel `𝒰_{s,u}` on two indices: the representation `K ⊗ K`
505 8. The deterministic core, `σ₁ ≠ σ₂`
655 6'. The one-index kernel and the short-range bilinear estimate (`σ
918 7'. The mixed signs: `K ⊗ K = (K ⊗ K - β² Θ ⊗ Θ) + β² Θ ⊗ Θ` and t
1503 12. Outside the window `(eq:ells_to_ellt2)` the whole term is a `
1605 14. The `u`-dependence of `f^{far}`: Lipschitz in `u`, the grid, 
1765 15. `f^{far}` uniformly in `u ∈ [s,t]`
2590 18. Comparisons at the size index `n`
2675 19. Two asymptotic facts (pure real analysis in `x = log W`)
2762 20. The real-level estimates for each case
3282 21. Eventual facts in `n`
```

Narrative (stage 1b began Thu Oct 8 10:38:32 UTC 2026; report written Thu Oct  8 12:26:26 UTC 2026):
- Route as in (a): `u`-uniform CLT by a grid `s + k(t-s)/N^{14}` and the worst sequence `t'_n` (`stCltFar_uniform`), whose hypotheses at `(s,t')` are `stIngR5_hyps_restrict`;
  `f^{far}` is Lipschitz in the propagator time through `Theta_sub_Theta` and the `∞→∞` norm; `|X|_max ≤ 4N` from `STLK` (`k = 2`) at `s`, w.h.p.
- The initial term: `σ₁ = σ₂` (`iniTermI_core_same`, `prop5Short_holds`; the case-(ii) comparison `𝒯_s ≤ e (m+1)^{d-2}𝒯_u` is replaced by one with `e^{√m}`, `iniTermI_Ts_le`);
  `σ₁ ≠ σ₂` with `ρ ≤ (log W)^{10}`: `iniTermI_core_lossy`; `ρ > (log W)^{10}`: window complement `iniTermI_mixed_tail` (`prop5Decay_holds`), window `iniTermI_mixed_bound`
  (`f^{near}` by `iniTermI_near` with the windowed convolution `iniTermI_W2`, Ward `iniTermI_ward` + `STAvgU` at `s`, `f^{far}` from `STCltFarUConcl`).
- `iniTermI_rl_all` collects the four cases at the real level; `iniTermI_concl` supplies the three events (`STDecay` at `D₁ = D + (7+τ)/𝔠 + 1`, `STAvgU` at `u = s`, `STCltFarUConcl`, each at `τ/4`),
  the eventual facts (`iniTermI_ev_K`, `iniTermI_ev_floor`, the two asymptotic lemmas) and `(con_st_ind)` (`iniTermI_rho_B`: `ρ_u ≤ (2A)^{𝔠_d}`, `ρ Bctl(s) ≤ 4 A^{-1/5}`).
- Heartbeats: `set_option maxHeartbeats 1000000` on 5 declarations and `4000000` on `iniTermI_concl`, each with a comment (long `calc` chains).
- Size: the file has 3823 lines against the ticket's stop rule at 2200 (size estimate 1100/1400/1900).  Stage 1b did not stop at the boundary because the pin
  `stIniTermI_holds` needs `stCltFar_uniform` and the lift, so a stop would have left it unproved; natural split points are the headings of §13 (line 1556), §16 (2131), §18 (2590).

## (c) Verified Mathlib names
- `add_pow_le` (`0 ≤ a → 0 ≤ b → (a+b)^n ≤ 2^(n-1) (a^n + b^n)`), `pow_add_pow_le` (`x^n + y^n ≤ (x+y)^n`, `n ≠ 0`): `#check` ok.
- `Real.pow_div_factorial_le_exp`, `Real.rpow_def_of_pos`, `Real.rpow_one_add'`, `Real.one_le_rpow`, `Real.sqrt_le_iff`, `Real.tendsto_log_atTop`: `#check` ok.
- `Finset.sum_filter_not_add_sum_filter`, `Finset.sum_union_inter`, `Finset.exists_max_image`, `Finset.single_le_sum`: ok; `MeasureTheory.measure_biUnion_finset_le`: ok.
- `Nat.ceil_le`, `Nat.ceil_lt_add_one`, `Matrix.linfty_opNorm_def`, `pow_le_pow_iff_left₀`, `le_of_pow_le_pow_left₀`: ok.
- Verified absent: `Real.sqrt_add_le`-type lemmas (`grep -rn sqrt_add_le Mathlib` has 0 hits; `iniTermI_sqrt_add_le` is proved from `Real.sqrt_le_iff`).

## (d) Open issues and paper-delta candidates
- `T2329a`: in regime (i) `ℓ_u < L`, so the case-(ii) comparison `B_{u,r} ≤ e 𝒯_u(r)` fails; `𝒯_s(|b₁-b₂|) ≤ (1+2^{d-1}) (m+1)^{d-2} e^{√m} 𝒯_u(|a₁-a₂|)`, `m = |b₁-a₁|+|b₂-a₂|`, closes against `Σ_x (|x|+1)^{d-2} e^{√|x|} e^{-c₀|x|} < ∞` (`iniTermI_Ts_le`, `iniTermI_sum_poly_exp_sqrt`).
- `T2329b`: `3_5:2173` states `lem;CLT` at the end time `t`; `(iksjuwjx)` needs it for every `u ∈ [s,t]` inside `P`.  New def `STCltFarUConcl` (index `Σ u ∈ [s,t], STCltFarIdx`, `ℓ_t ↦ ℓ_u`);
  `stCltFar_uniform` derives it from `stCltFar_holds` (the merged pin is unchanged).
- `T2329c`: the factor `(1-s)²` of `(iksjuwjx)` is `((u-s)/u)² ≤ (1-s)²` in the exact expansion `(eq:decompU)`: `c ∈ [0,1]` in `iniTermI_core_mixed` (same remark as `T2163a/b` of case (ii)).
- `T2329d`: `lem;CLT` is applied to the sequence `t'_n = s_{k*_n}` that maximises the failure probability over the grid (`Finset.exists_max_image`); the paper's "uniformly in `u`" is this argument plus the Lipschitz bound of `f^{far}` in `ξ = u`.
- `T2329e`: the window complement `(eq:ells_to_ellt2)` uses `prop:ThfadC` in its linear-exponential form (`iniTermI_theta_far`, from `prop5Decay_holds`), not the `e^{-√}` form of `step5Kernel_theta_decay` (as flagged in (a), (ii)(4)).
- Observation: the registry line of `STIniTermI` is deleted as the ticket says; `RBM3D.lean` is untouched (the hub adds the import and the pre-existing full-build audit then passes, see above).
- Observation: `iniTermI_near` needs only the `ℓ_∞` windowed convolution `iniTermI_W2` and the ball sum `iniTermI_ball_PI`; no `log` appears for `d = 4` (cf. (a), (ii)(6)).
- Open: none for the targets; the file is large (see Size) and may be split at the headings above if the dispatcher wants smaller modules.
