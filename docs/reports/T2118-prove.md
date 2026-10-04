Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 07:09:13 UTC 2026

Notation: `P_D(x) = STprof(x) = W^{-d}𝒯̃^ℓ_{t,D}(x)` (`Step2Defs.lean:75`), `𝒯(ρ)=B_ρ e^{-√(ρ/ℓ_t)}` (`Defs/Tail.lean:44-52`), `u=1-t`, `a,b` the labels, `r=|a-b|_∞>ℓ†`, `Reg = {ℓ*<|c-a|≤ℓ, ℓ*<|c'-b|≤ℓ, |c-c'|≤1}` (`emn2ExpS3`, `EMn2Exp1.lean:408`), `Ĵ=STJhatM`, `N=(WL)^d`. Scripts in `scratchpad/T2118/`.

### (i) Proof map and exponent table

Route of `S̃₃` (paper `3_5:871-888`), all steps deterministic, eventually in `n`, no `STLWassmExp` and no `(GijGEX)` used:
- H1 Hölder (new, needs `H` Hermitian): `|𝓛⁶| ≤ ∏_{i=1}^6 (𝓛²_{(σ_i,-σ_i),(a_i,a_{i+1})})^{1/2}` (`|tr X₁…X₆| ≤ ∏‖X_i‖_HS`, `‖XY‖_HS ≤ ‖X‖_HS‖Y‖_HS`); the cyclic pairs are `(a,b),(b,c'),(c',b),(b,a),(a,c),(c,a)`, so each of `|a-b|,|b-c'|,|a-c|` occurs twice and the product is `∏ ‖𝓛²‖^{1/2} = Y_ab Y_bc' Y_ac`.
- H2 `(eq_L2-J)`: `‖𝓛²_{(s,-s),(x,y)}‖ ≤ ‖(𝓛-𝒦)²‖ + ‖𝒦²‖ ≤ Ĵ P_D(x,y) + W^{-d}‖Θ_u(x,y)‖` (`Ĵ` is a sup over all `σ`, all pairs: `Step2Defs.lean:81`); `KLK_two` (`Loop/KLTree.lean:211`) with `m_s m_{-s}=|m|²=1` gives `‖𝒦²‖=W^{-d}‖Θ_u(x,y)‖`; `emn2Exp_kellStar_far` (δ=1) gives `‖Θ_u‖ ≤ W^{-D_K}` for `|x-y|>ℓ*`, true for all three distances on `Reg` and `r>ℓ†>ℓ*`. Hence `‖𝓛²‖ ≤ (Ĵ+ε_K)P_D`, `ε_K=W^{-d}`, using `P_D ≥ W^{-d-D}` and `D_K=D+2d`.
- H3 `|SB|≤1`, `3^d` partners `c∼c'`; `P(|a-c|) ≤ K₁P(|a-c'|)` with `K₁=2^{d-2}e` (one-step shift, `|a-c|≥ℓ*>1` so no `ρ=0`; `P=W^{-d}max(𝒯,W^{-D})` and `max` is monotone).
- H4 `P ≤ W^{-d}(𝒯+W^{-D})`: `Σ_{c'}P(b,c')P(a,c') ≤ W^{-2d}[Σ𝒯𝒯 + W^{-D}(Σ𝒯+Σ𝒯) + W^{-2D}|Reg|]`; `Σ𝒯𝒯 ≤ C_I u⁻¹𝒯(r)` by `ekPropTInf_holds` (`Evolution/PropTInf.lean:534`, `u=t`), `Σ𝒯 ≤ C₁u⁻¹` (`Σ_c(L^du)⁻¹=u⁻¹`, `Aℓ_t² ≤ u⁻¹`, `pti_sum_radial` `PropTInf.lean:88` is private, so a new private lemma at `|·|_∞`; not merged).
- H5 `u⁻¹ = Im m(E)/η ≤ η⁻¹` (`etaT=(1-t)Im m`, `Loop/GLoop.lean:75`, `Im m ≤ 1`); `(Ĵ+ε_K)³ ≤ 4(Ĵ³+ε_K³)`, `ε_K³=W^{-3d} ≤ Bctl^{1/2}`. Result: `S̃₃ ≤ C_n η⁻¹(Bctl^{1/2}+Ĵ³)P_D(r)²` with `C_n ≤ N^{τ}` eventually, provided the floor-floor row below.

| row | value | constraint | slack |
|---|---|---|---|
| 1 `D_K` | `D+2d` | `W^{-d-D_K} ≤ ε_K W^{-d-D}` with `ε_K=W^{-d}` | `W^{-d}` |
| 2 kellStar premises | `δ=1, Λ=𝔡⁻¹, τ=ε/2` | `SizeTendsto, Bandwidth 𝔠, RangeCond τ t, t<1, 0<λ≤Λ` (from `STFlow`: `locDomain`, `WO`); `u ≥ 1-lemT ≥ Im z/(1+‖z‖)` (`ST_one_sub_lemT`, `Step2Iterate.lean:1014`) `≥ N^{-1+ε}/4 ≥ N^{-1+ε/2}` iff `N^{ε/2} ≥ 4` | eventual |
| 3 `ε_K³` | `W^{-3d}` | `≤ Bctl^{1/2}`, `Bctl ≥ c_B W^{-d}` (`ST_Bdata_holds`) | `W^{-5d/2}` |
| 4 `K₁` | `2^{d-2}e` | `𝒯(ρ) ≤ K₁𝒯(ρ+1)`, `ρ≥0`, `ℓ_t≥1` (`B` ratio `((ρ+2)/(ρ+1))^{d-2}`, `exp(√((ρ+1)/ℓ_t)-√(ρ/ℓ_t)) ≤ e`) | `0` at `ρ=0` (sharp) |
| 5 `C_I, C₁` | depend on `d` only | (TTT2) hyp. `0≤t<1, g>0`, (i) `u ≥ g²/L²`: holds on the far set (below) | — |
| 6 `|Reg|` | `≤ min(L,2ℓ+1)^d ≤ (3(log W)^{10}ℓ_t)^d` | `ℓ ≤ (log W)^{10}ℓ_t` (pin) | polylog `≤ N^τ` |
| 7 floor-floor | `u|Reg|W^{-D}` | `≤ N^{τ}`; if `ℓ_t=1` trivial; if `ℓ_t=g/√u>1`: `u ℓ_t^d = g²ℓ_t^{d-2}`, so **`D ≥ log_W(g²ℓ_t^{d-2}) + o(1)`**; sufficient `D ≥ (d-2)/(d𝔠)` (`ℓ_t ≤ L`, `L^d ≤ N ≤ W^{1/𝔠}`, `g ≤ 𝔡⁻¹`) | `D-(d-2)/(d𝔠)`; **none for small `D`** |
| 8 loss | `4·3^dK₁(C_I+2C₁+1)` `·` polylog | `≤ N^{τ}` for each fixed `τ` | arbitrary |
| 9 `Ĵ` | `≥ 0` | `Bctl^{1/2}+Ĵ³ ≥ Bctl^{1/2}` | — |

§29 checks. (1) `0 ≤ t ≤ lemT`: used for `η>0`, `u ≥ N^{-1+ε}/4`, `ST_Bdata_holds`. (2) Regimes (`ℓ_t = min(max(g/√u,1),L)`): `u ≥ g²`: `ℓ_t=1`, `(i)` holds, row 7 trivial. `g²/L² < u < g²`: `ℓ_t=g/√u ∈ (1,L)`, `(i)` holds, row 7 active. `u ≤ g²/L²` (includes `u ≤ g²/L^d`) or `g > L`: `ℓ_t = L`, `ℓ† = (log W)^{7/4}L ≥ L ≥ zdistInf`, the far set is empty and `S̃₃·1_far ≡ 0` (`(ii)` of (TTT2) is never needed). `Σ_a𝒯_t ≤ C/u` in all regimes (argument in H4; script: finite). (3) `L^d ≤ W^K` is not assumed; only `Bandwidth` (in `STFlow`) enters row 7. (4) `Prec` eventual, constants depend on `d, 𝔡` only (`C_I, C₁, K₁, c_B`), the scale gap `2(ℓ*+1) ≤ ℓ†` eventual (T2109a).

### (ii) Instance, regimes and numerical checks

Instance of every hypothesis of target 1 and 2 at once (`d=3`, `sz0`: `L=4(n+1), W=(2(n+1))^5, λ=(2(n+1))^{-6}`; `κ=ε=𝔡=1/10, 𝔠=1/6`; `z_n=1/2+iN^{-4/5}`; `ℓ_n=2ℓ*` (inside `[ℓ*, (log W)^{10}ℓ_t]`); `D=4`). `Reg` nonempty: the midpoint `c` of `a,b` at `|a-b|=ℓ†+1` has `|c-a|=|c-b|≈ℓ†/2 ∈ (ℓ*,ℓ]`. Case C is `sz0.withLam (fun _ => 1/2)` (`λ` is a free sequence of `Sizes`, `Defs/Sizes.lean:182`), `t_n=1-g²/ℓ_t²`, which makes row 7 active.
```
$ python3 inst_c.py     # high-precision, every named hypothesis checked: 0≤t≤lemT, locDomain, Bandwidth, WO, RangeCond, far window ℓ†<L/2, (TTT2)(i), 2(ℓ*+1)≤ℓ†, W^{-3d}≤Bctl^{1/2}, Reg nonempty
A n=188 t=1/16 lam=sz0: L=756 logW=29.7 logN=109 g=3.4e-16 1-t=9.38e-01 ell_t=1 ell^dag=377.3 L/2=378.0; all hypotheses True: True []
    D0_route = log_W(g^2 ell_t^(d-2)) = -2.400; D=0.05 closes: True; D=4 closes: True; sufficient (d-2)/(d c)=2 <= 4: True
B n=1e6 t=1/16 lam=sz0: L=4000004 logW=72.5 logN=263 g=1.6e-38 1-t=9.38e-01 ell_t=1 ell^dag=1803 L/2=2000002.0; all hypotheses True: True []
    D0_route = log_W(g^2 ell_t^(d-2)) = -2.400; D=0.05 closes: True; D=4 closes: True; sufficient (d-2)/(d c)=2 <= 4: True
C n=1e9 lam=1/2 t=1-g^2/ell_t^2: L=4000000004 logW=107.1 logN=388 g=5.0e-01 1-t=1.00e-12 ell_t=5e+05 ell^dag=1.782e+09 L/2=2000000002.0; all hypotheses True: True []
    D0_route = log_W(g^2 ell_t^(d-2)) = +0.110; D=0.05 closes: False; D=4 closes: True; sufficient (d-2)/(d c)=2 <= 4: True
```
`D=4` closes in A, B, C; `D=0.05` fails in C (A, B have `g` tiny, so `g²ℓ_t^{d-2}` is tiny). (A `n=188` is the first `n` with a nonempty far window, as T2109 (a).)

(TTT2) and `Σ𝒯`, `d=3`, `g=1/2`, torus `L^∞`, all `a,b` (translation invariance, FFT). `T=𝒯_t`, `P=max(T,W^{-D})` at `W=2` over all `c`:
```
$ python3 ttt2.py | head -12 | cut -c1-175
L=8 g=0.5 1-t=0.1 ell_t=1.58 regime(g^2/L^2=3.91e-03<1-t: True) max_b conv/((1-t)^-1 T(b))=19.917  (1-t)*sum_c T=11.151
    floor W^-D, W=2.0 D=0.1: max_b sum_c P(c)P(b-c)/((1-t)^-1 P(b)) = 48.160
    floor W^-D, W=2.0 D=4.0: max_b sum_c P(c)P(b-c)/((1-t)^-1 P(b)) = 19.917
L=8 g=0.5 1-t=0.001 ell_t=8.00 regime(g^2/L^2=3.91e-03<1-t: False) max_b conv/((1-t)^-1 T(b))=1.045  (1-t)*sum_c T=0.851
    floor W^-D, W=2.0 D=0.1: max_b sum_c P(c)P(b-c)/((1-t)^-1 P(b)) = 1.045
    floor W^-D, W=2.0 D=4.0: max_b sum_c P(c)P(b-c)/((1-t)^-1 P(b)) = 1.045
L=16 g=0.5 1-t=0.1 ell_t=1.58 regime(g^2/L^2=9.77e-04<1-t: True) max_b conv/((1-t)^-1 T(b))=66.408  (1-t)*sum_c T=30.995
    floor W^-D, W=2.0 D=0.1: max_b sum_c P(c)P(b-c)/((1-t)^-1 P(b)) = 382.556
    floor W^-D, W=2.0 D=4.0: max_b sum_c P(c)P(b-c)/((1-t)^-1 P(b)) = 49.727
L=16 g=0.5 1-t=0.001 ell_t=15.81 regime(g^2/L^2=9.77e-04<1-t: True) max_b conv/((1-t)^-1 T(b))=2.777  (1-t)*sum_c T=1.960
    floor W^-D, W=2.0 D=0.1: max_b sum_c P(c)P(b-c)/((1-t)^-1 P(b)) = 3.907
    floor W^-D, W=2.0 D=4.0: max_b sum_c P(c)P(b-c)/((1-t)^-1 P(b)) = 2.777
```
The ratios are finite, equal the pure `𝒯` ratio for `D=4`, and grow with `L` at `1-t=0.1` (merged constant `C_d`; no claim on its value); the floor `D=0.1` raises them (the floor-floor term, row 7). `(1-t)Σ_c𝒯` is finite in all four cases.

`K₁` shift (`python3 shift1.py`): `max 𝒯(ρ)/𝒯(ρ+1)/(2^{d-2}e) = 1.0000000000000002` over 400000 random `(d∈[3,6], L, g, 1-t, ρ)`, at `ρ=0` (equality up to rounding).

One sample of `S̃₃` (`python3 s3.py <λ> 1 2`; `d=3, L=4, W=2, N=512, t=1/16, z=1/2+iN^{-4/5}, D=4, ℓ=2`, literal block sums, exact `𝒦=W^{-d}m_{σ₁}m_{σ₂}(1-t m_{σ₁}m_{σ₂}S)^{-1}`, `Ĵ` over all four `σ` and all pairs, 16128 cases `(σ,a,b)`, `|a-b|>ℓ†`; finite-size sanity check, `ℓ>(log W)^{10}ℓ_t` is not in force at `W=2`):
```
lam=1/64: Jhat=0.1204 y2=1.0188; max S3/Holder-route=7.148e-02 (<=1)  max S3/[eta^-1(Bctl^1/2+Jhat^3)P^2]=3.902e-13
lam=1   : Jhat=0.1066 y2=1.9285; max S3/Holder-route=4.367e-02 (<=1)  max S3/[eta^-1(Bctl^1/2+Jhat^3)P^2]=2.872e-04
```
Premise-consistent test of row 7 (`python3 holder_route.py 40`): `W=10^{10^{40}}`, `d=3`, `g=1/2`, `ℓ_t=W^{0.3}`, `u=g²/ℓ_t²`, `ℓ†<L/2`, `r=1.01ℓ†`, 2-loop profile `Y=min(Ĵ P_D, P_{D₁})`, `D₁=100` (satisfies `Y ≤ P_{D'}` for all `D'`, so every `STLWassmExp` and `Ĵ` hold), `Ĵ=W^{-j}`; the Hölder bound `W^dΣ_{c∈ sub-cube⊂Reg} Y_abY_acY_bc'` over the pin's RHS `η⁻¹(Bctl^{1/2}+Ĵ³)P_D(r)²`, exponent `log_W`:
```
lam=0.3 D=0.05: j=0.0:-0.500 j=0.25:+0.250 j=0.5:+0.250 j=0.75:-0.500 j=1.0:-1.250 j=2.0:-4.250  max=+0.250
lam=0.3 D=0.1: j=0.0:-0.400 j=0.25:+0.200 j=0.5:+0.200 j=0.75:-0.550 j=1.0:-1.300 j=2.0:-4.300  max=+0.200
lam=0.3 D=0.2: j=0.0:-0.200 j=0.25:+0.100 j=0.5:+0.100 j=0.75:-0.650 j=1.0:-1.400 j=2.0:-4.400  max=+0.100
lam=0.3 D=0.28: j=0.0:-0.040 j=0.25:+0.020 j=0.5:+0.020 j=0.75:-0.730 j=1.0:-1.480 j=2.0:-4.480  max=+0.020
lam=0.3 D=0.35: j=0.0:-0.000 j=0.25:-0.000 j=0.5:-0.000 j=0.75:-0.750 j=1.0:-1.500 j=2.0:-4.500  max=-0.000
lam=0.3 D=1.0: j=0.0:-0.000 j=0.25:-0.000 j=0.5:-0.000 j=0.75:-0.750 j=1.0:-1.500 j=2.0:-4.500  max=-0.000
```
The excess is `W^{(d-2)λ-D}` for `D<(d-2)λ`: the paper's chain `(eq:boundwtS31)`→`3_5:888` (and every pointwise-Hölder route fed by `‖𝓛²‖ ≤ ĴP_D`) overshoots the pin's RHS when the floor `W^{-D}` dominates `𝒯` on `Reg`.

External hypotheses (lesson 14): none new; `STLWassmExp`, `STInitialGT2` are not used by `S̃₃`; `ekPropTInf_holds`, `stK2decay_holds`, `kellStarEv` are merged theorems.

### Verdicts
- Target 1 (`h3`, `∀ D>0`): **FAIL as pinned.** Rows 1-6, 8, 9 close; row 7 does not for `D < log_W(g²ℓ_t^{d-2})` (up to `(d-2)/(d𝔠)`), an admissible regime (case C: `λ≡1/2`, `ℓ_t=5·10^5`). The paper states the estimate "for any large constant `D`" (`3_5:437`), the pin `STEMn2Exp` (`Step2Defs.lean:456`) and `h3` (`EMn2Exp1.lean:1715`) say `∀ D>0`. For `D ≥ (d-2)/(d𝔠)` the route closes (cases A, B, C at `D=4`). I do not claim `STEMn2Exp` false at small `D`; I claim the route, and every route from `‖𝓛²‖ ≤ ĴP_D`, does not prove it.
- Target 2 (`stEMn2Exp_holds`): **FAIL as pinned**, same reason (`emn2Exp_near`, `emn2Exp_far12` are fine for all `D>0`).
- Needed from the dispatcher: a primed pin `STEMn2Exp'` (and `h3'`) with the premise `(d-2)/(d*𝔠) ≤ D` (or `∀ᶠ n, g²L^{d-2} ≤ W^{D}`) after `∀ D`; `ST_LW_sections` (`Step2Events.lean:462`) passes its own `D` to `hEMe`, so its consumers need `D ≥ (d-2)/(d𝔠)` too (paper-delta candidate `T2118a`). With it the work is: 6-loop Hölder, one new private lemma `Σ_c𝒯(|c|_∞) ≤ C/(1-t)`, the shift `K₁`, assembly; no `(GijGEX)`.

## (a′) Math preflight, split route (Amend 1, restart at stage 1a) — Sun Oct  4 08:01:30 UTC 2026

(a) above is unchanged; row 7 (floor-floor) is retired by the split, rows 1-6, 8, 9 are reused for `A^n`. Notation as in (a); `Pf=emn2ExpPf` (`EMn2Exp1.lean:180`), `r=|a-b|_∞>ℓ†`, `y²=N^{τ/5}` (as `emn2Exp_far12`). Scripts in `scratchpad/T2118/` (`split_inst.py` and `expo.py` are the Fable scripts `docs/claude-team/fable/2026-10-04-emn2exp-D-{split,exponents}.py` rerun/imported unchanged; `s3split.py`, `sumT.py` new).

### (i) Exponent table, split route

Split of `emn2ExpS3` (`:408-415`) by the indicator `Pf(|c'-b|) ≤ Pf(r)` (`A^f`) vs `>` (`A^n`); the two sums are disjoint and add to `S̃₃`.

- **A^f (contraction, no sum over `c`, no `Ĵ`, no `D`).** `emn2Exp_part1` (`:502-598`) with the set `𝒜 = {c' ∈ A^f : ∃ c∼c', ℓ*<|c-a|≤ℓ, ℓ*<|c'-b|≤ℓ}`, `M=y²Pf(r)`, `K=1`: `hM` = `emn2Poly_norm_loop4_alt_le` (`‖𝓛⁴_{(c',b,c',b)}‖^{1/2} ≤ ‖𝓛²_{(σ₀,-σ₀),(c',b)}‖`) + `h2` (`‖𝓛²_{(s,-s)}‖ ≤ y²Pf`, from `STLWassmExp` at the pin's own `D`) + `Pf(|c'-b|) ≤ Pf(r)` (definition of `A^f`); `stContractPt_holds` (`ContractPt.lean:463`, `Step2Defs.lean:391`) then `emn2Exp_loop3_ctrl` (`:482`). Result `S̃₃^f ≤ 3^d η⁻¹ y⁵ √Pf(0) Pf(r)²` (`z.im=etaT`, `etaT_eq_zt_im`, used at `:1546`); `√Pf(0) ≤ √(1+c_B⁻¹)Bctl^{1/2}` (`ST_prof_le_Bctl`, as `:1572`); `y⁵=N^{τ/2}`.
- **A^n (Hölder).** `Pf(|c'-b|)>Pf(r) ≥ W^{-d-D}` forces `𝒯(|c'-b|)>W^{-D}` (and `>𝒯(r∧ℓ)`), so `Pf(|c'-b|)=W^{-d}𝒯(|c'-b|)`, a genuine tail. Legs: rows H1-H3 of (a) (all three distances `>ℓ*`), `Y_ab Y_bc' Y_ac ≤ (Ĵ+ε_K)³Pf(r)Pf(|b-c'|)Pf(|a-c|)`. Sum: `W^d Σ_{c'∈A^n} Σ_{c∼c'} … ≤ W^{-d}·3^dK₁·Pf(r)(Ĵ+ε_K)³ Σ_c 𝒯(|c-b|)(𝒯(|a-c|)+W^{-D})` (shift row 4 for `c'→c`, `|c-b|≤|c'-b|+1`) `≤ 3^dK₁(C_I𝒯(r)+C₁W^{-D})u⁻¹ …` by `ekPropTInf_holds` (`PropTInf.lean:534`, `u:=t`, regime clause `g²/L²≤1-t ∨ 1-t≤g²/L²` is a tautology) and `Σ_c𝒯_t(|c|_∞) ≤ C₁/(1-t)` (new private lemma, row 5 of (a)). `W^{-D}Σ_c𝒯` appears once; the floor-floor `W^{-2D}|Reg|` never occurs because the `(b,c')` factor is `W^{-d}𝒯`, not the floor. Result `S̃₃^n ≤ 2·3^dK₁(C_I+C₁)(Ĵ+ε_K)³ u⁻¹ Pf(r)²`, `(Ĵ+ε_K)³ ≤ 4Ĵ³+4ε_K³`, `u⁻¹=Im m/η ≤ η⁻¹`.

| row | value | constraint | slack |
|---|---|---|---|
| f1 | `3^d y⁵ √Pf(0)` | `≤ N^{τ} Bctl^{1/2}` with `√Pf(0) ≤ √(1+c_B⁻¹)Bctl^{1/2}` | `N^{τ/2}` (y⁵=N^{τ/2}); `3^d`, `c_B` are `d`-only |
| f2 `A^f` hypothesis `hM` | `M=y²Pf(r)`, `K=1` | `Pf(|c'-b|) ≤ Pf(r)` on `𝒜` (definition of `A^f`; no distance case split since `Pf(|c'-b|)≤Pf(r)` is assumed) | none needed: `0` |
| f3 `D` | any `D>0` | none (no row-7 condition) | all `D>0` |
| n1-n6, n8, n9 | rows 1-6, 8, 9 of (a) | as in (a) (`D_K=D+2d`, kellStar premises, `ε_K³≤Bctl^{1/2}`, `K₁=2^{d-2}e`, `C_I,C₁`, `|Reg|` not needed now, loss `≤N^τ`) | as in (a) |
| n7 `ε_K` vs `Pf` on `A^n` | `Pf(|·|)≥W^{-d-D}` on all three legs | `‖𝒦²‖ ≤ W^{-d-D_K} ≤ ε_K W^{-d-D}` | `W^{-d}` |
| n10 floor sum | `W^{-D}Σ_c𝒯 ≤ C₁W^{-D}/u` | `≤ C₁ u⁻¹ Pf(r)W^{d}` since `Pf(r) ≥ W^{-d-D}` | exact |
| n11 cover | `A^f ⊔ A^n` | `emn2Exp_cover` (`:419`) already reduces to `S̃₁+S̃₂+S̃₃` | — |

Exponent bookkeeping (`expo.py`, `ℓ_t=W^λ`, `u=W^{-2λ}`, `Ĵ=W^{-j}`, `d=3`, `D` arbitrary; excess = `log_W(bound/pin RHS)`, `≤0` closes; PF = preflight route row 7, SF = `A^f`, SN = `A^n`):
```
$ python3 expo.py | sed -n 3,8p | sed 's/ *j=0 .*|/ |/'     (lam=0.3 block; the per-j columns are cut)
D=0.05 : | max PF=+0.250 max SF=+0.000 max SN=+0.000
D=0.1  : | max PF=+0.200 max SF=+0.000 max SN=+0.000
D=0.2  : | max PF=+0.100 max SF=+0.000 max SN=+0.000
D=0.28 : | max PF=+0.020 max SF=+0.000 max SN=+0.000
D=0.35 : | max PF=-0.100 max SF=+0.000 max SN=+0.000
D=1    : | max PF=-1.400 max SF=+0.000 max SN=+0.000
```
(By hand: `SF = -d/2 - max(-d/2,-3j) ≤ 0`, `SN = -3j - max(-d/2,-3j) ≤ 0` for every `D, j, λ`, from `expo.py:34-37`.) The remaining non-monotonicity of `Ĵ_D³P_D²` in `D` is irrelevant: the pin is proved at each `D` directly.

§29 checks: (1) `0≤t≤lemT`: as (a) (`η>0`, `u≥N^{-1+ε/2}`). (2) Regimes: `u ≥ g²`: `ℓ_t=1`; `g²/L²<u<g²`: `ℓ_t=g/√u`, the `A^n` sums need `(TTT2)` and `Σ𝒯≤C₁/u`, both `d`-only; `u ≤ g²/L²`: `ℓ†≥L/2`, far set empty (as (a)); for `A^f` no regime enters. (3) No `L^d≤W^K`. (4) `Prec` eventual; constants `3^d, K₁, C_I, C₁, c_B, 4` are `W,L,λ,D`-free. Dependencies: no `(GijGEX)`, no new external hypothesis.

### (ii) Instance and numerical checks

Instance of all hypotheses of targets 1-2 at once, `D=0.05` (the case that failed): case C of (a) (`d=3`, `λ≡1/2`, `ℓ_t=5·10^5`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `n=10^9`), rerun:
```
$ python3 inst_c.py | tail -2     (verbatim)
C n=1e9 lam=1/2 t=1-g^2/ell_t^2: L=4000000004 logW=107.1 logN=388 g=5.0e-01 1-t=1.00e-12 ell_t=5e+05 ell^dag=1.782e+09 L/2=2000000002.0; all hypotheses True: True []
    D0_route = log_W(g^2 ell_t^(d-2)) = +0.110; D=0.05 closes: False; D=4 closes: True; sufficient (d-2)/(d c)=2 <= 4: True
```
(`D0_route` is the retired row 7, shown only for contrast; the split has no `D`-condition.) At this instance `D=0.05<D0_route`: the floor `W^{-0.05}` exceeds `𝒯` on `|c'-b|≥ρ_D`, so `A^f` contains that whole zone and `A^n` is the inner shell, which is the case the paper's chain could not close. Case C is an exponent-level instance (astronomically large `n`); the finite-size checks below are the numbers.

Brute force, `d=3`, `g=1/2`, torus `L^∞`, all `b` with `|b|>ℓ†`; `H=Σ_Reg Pf(|b-c'|)Pf(|a-c|)`, `Hn`=same restricted to `A^n`, `Hf=H-Hn`; `R0+R1` = the `(TTT2)`-shape bound plus `3^d u Σ_c𝒯` (no floor), `ok` = `u·Hn/P(r) ≤ R0+R1` (`ℓ*,ℓ†,ℓ` are free finite-size parameters here; `L=8` has no far window since `ℓ†≥2(ℓ*+1)≥4=L/2`, and `1-t=10⁻³` at `L=16` has `ℓ_t=15.8>L/2`, far set empty):
```
$ python3 split_inst.py     (excerpt of 14 rows, columns abbreviated with `...`; 1-t=0.1, l_t=1.58; floor F=W^-D)
 L= 16 ... F=1.0e-06 | Hoelder route u*H/P(r)= 955.6 | split: u*Hn/P(r)= 812.2 <= R0+R1=1242.1+836.9 ok ; u*Hf/P(r)= 208.6
 L= 16 ... F=5.0e-02 | Hoelder route u*H/P(r)= 874.3 | split: u*Hn/P(r)= 725.0 <= R0+R1=1242.1+836.9 ok ; u*Hf/P(r)= 213.4
 L= 16 ... F=2.0e-01 | Hoelder route u*H/P(r)=1445.2 | split: u*Hn/P(r)=   0.0 <= R0+R1=1242.1+836.9 ok ; u*Hf/P(r)=1445.2
 L= 32 ... F=1.0e-02 | Hoelder route u*H/P(r)=3300.5 | split: u*Hn/P(r)=2849.2 <= R0+R1=4452.2+1873.5 ok ; u*Hf/P(r)= 817.2
 L= 32 ... F=2.0e-01 | Hoelder route u*H/P(r)=14797.8| split: u*Hn/P(r)=   0.0 <= R0+R1=4452.2+1873.5 ok ; u*Hf/P(r)=14797.8
 L= 64 u=0.001 l_t=15.81 ... F=1.0e-06 | ... split: u*Hn/P(r)= 425.6 <= R0+R1=540.0+415.8 ok
```
`u·Hn/P(r)` stays within `R0+R1` in every row of `split_inst.py` (12 rows with `1-t=0.1`, 2 with `1-t=10⁻³`); `u·Hf/P(r)` (what Hölder would need on `A^f`) grows with `L` and `F`, the contraction route has no such sum. `Σ_c𝒯` finite and saturating in `L` (`sumT.py`, `(1-t)Σ_c𝒯`, `d=3`, `g=1/2`):
```
1-t=0.1   ['L=16: 30.995', 'L=32: 69.388', 'L=64: 121.428', 'L=128: 165.830', 'L=256: 186.244']
1-t=0.01  ['L=16: 9.163', 'L=32: 26.223', 'L=64: 63.804', 'L=128: 126.396', 'L=256: 198.440']
1-t=0.001 ['L=16: 1.960', 'L=32: 5.354', 'L=64: 15.400', 'L=128: 40.200', 'L=256: 89.234']
```
The `(TTT2)` convolution at `L∈{8,16}`, `1-t∈{0.1,10⁻³}`, all `a,b` is in (a) (`ttt2.py`; unchanged, constants 19.9, 1.05, 66.4, 2.78).

One literal sample of both parts (`d=3, L=4, W=2, N=512, t=1/16, z=1/2+iN^{-4/5}, ℓ=2, λ=1`, literal block sums, `16128` cases `(σ,a,b)`, `|a-b|>ℓ†`; `y²=max‖𝓛²_{(s,-s)}‖/Pf`; Hölder = the six-square-root product restricted to the region):
```
$ python3 s3split.py 1 2 2 <D>
D=0.05: y2=1.0656 max #R3&A^f=1675 max #R3&A^n=0   max S3^f/[3^d eta^-1 y^5 sqrt(P(0)) P(r)^2]=6.079e-08  max S3^n/Holder(A^n)=0 (A^n empty)
D=1.0 : y2=1.9318 max #R3&A^f=1675 max #R3&A^n=0   max S3^f/[...]=6.903e-08                              max S3^n/Holder(A^n)=0 (A^n empty)
D=4.0 : y2=1.9318 max #R3&A^f=1675 max #R3&A^n=694 max S3^f/[...]=1.636e-06                              max S3^n/Holder(A^n)=3.516e-02
```
Both bounds hold (`≤1`) with `A^f`, `A^n` both nonempty at `D=4`; at small `D` the floor makes `A^n` empty and `S̃₃=S̃₃^f`, carried by the contraction alone. External hypotheses (lesson 14): none new; `STLWassmExp` is used only through `h2` at the pin's `D`; `ekPropTInf_holds`, `emn2Exp_kellStar_far`, `stContractPt_holds` are merged theorems.

### Verdicts
- **Target 1 (`h3` of `emn2Exp_of_far3`, `∀ D>0`): PASS** for the split route. `A^f` closes by `emn2Exp_part1` with region `A^f`, `K=1` for every `D>0`; `A^n` closes by Hölder + `(TTT2)` + `Σ_c𝒯≤C₁/(1-t)` with excess `≤0` for every `D,j,λ` (SF, SN rows). New pieces versus (a): the region lemma for `A^f` (copy of `emn2Exp_part1`, `hK` replaced by the region's definition) and the split of `emn2ExpS3M`; no `(GijGEX)`, no restatement of the pin.
- **Target 2 (`stEMn2Exp_holds`): PASS**, `emn2Exp_of_far3` applied to target 1 (`emn2Exp_near`, `emn2Exp_far12` merged).
- Paper-delta candidate `T2118a`: `3_5:881-886` consumes the "large `D`" (`W^{-2D}Σ_c 1`, `D ≥ (d-2)log_W ℓ_t`); the formalization splits `S̃₃` at `Pf(|c'-b|) ≤ Pf(|a-b|)` and bounds the floor part by the contraction inequality as in `S̃₁`, so `(eq:MG_conclusion3)` holds for every `D>0`.
- Not re-derived here by independent means: the Hölder step H1 and the new private lemma `Σ_c𝒯 ≤ C₁/(1-t)`; the checks above are numerical.

## (a″) Preflight corrections — Sun Oct  4 10:19:41 UTC 2026

One omission; the mathematics of (a)/(a′) is unchanged and holds for `d ≥ 3`, the paper's range.
- Neither (a), (a′) nor the ticket's target 2 (`stEMn2Exp_holds (d : ℕ) : STEMn2Exp d`) carry `3 ≤ d`, but two inputs of the route do: `KellStarEv` (`Path/KellStar.lean:55`, `… 3 ≤ d → 0 < 𝔠 → …`; used for `(eq_L2-J)`) and `EKPropTInf := 3 ≤ d → …` (`Evolution/PropTInf.lean:523`; used for `(TTT2)`).  The pin `STEMn2Exp` (`Step2Defs.lean:456`) has no such premise, its consumers do (`STNewKLK`, `STK2decay`, `STStep2`: `Step2Defs.lean:378, 569, 600`).  This is the case of DECISIONS §31 (T2080 entry: the two bridges get `(hd : 3 ≤ d)`, no pin text changes).  So targets 1-2 are delivered as `emn2Exp_far3 (d) (hd : 3 ≤ d)` and `stEMn2Exp_holds (d) (hd : 3 ≤ d)`.  For `d ∈ {1, 2}` I have neither a proof (no `Θ` decay beyond `ℓ*` and no `(TTT2)` in the merged files) nor a counterexample.  Decision needed: (d) 1.
- (a) row 1 / (a′) row n7: `D_K = D + d` suffices (not `D + 2d`): `‖𝒦^{(2)}‖ = W^{-d}‖Θ‖ ≤ W^{-d} W^{-(D+d)} ≤ W^{-d} P` since `P ≥ W^{-d-D}` (`emn2Exp2_loop2_far_le`).  Verdicts unchanged.

## (b) Script output — Sun Oct  4 10:26:34 UTC 2026

Branch `t/T2118`, commit `e9983a2` (one commit on `471b643` = `main` at T2125; `main` is now `dd1748c`; `git diff 471b643 main --stat -- <the two files>` is empty), worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2118`, scripts in `scratchpad/T2118/`.  New file `RBM3D/Induction/EMn2Exp2.lean` (1295 lines: 5 public theorems, 32 private declarations, 6 `example`s); `RBM3D/Test/Axioms.lean`: the registry line `STEMn2Exp` removed; `RBM3D.lean` untouched (the root import is the hub's; added temporarily for the full build below, reverted).

### b.1 Build, axioms, statements
```
$ lake build RBM3D.Induction.EMn2Exp2 2>&1 | tail -2     # after the last edit of the file
✔ [3769/3769] Built RBM3D.Induction.EMn2Exp2 (8.6s)
Build completed successfully (3769 jobs).
$ lake env lean RBM3D/Induction/EMn2Exp2.lean; echo "exit $?"     # standalone, all linters on, no warning
exit 0
$ lake env lean axioms.lean     # #print axioms of the 5 public declarations
'RBM.Gauss.Sizes.emn2Exp2_loop6_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp2_S3_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp2_loop2_far_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Exp_far3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stEMn2Exp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build     # 10:24 UTC on 471b643 + this commit; RBM3D.lean temporarily with the root import of the module
info: RBM3D.lean:174:0: axiom audit: 3889 theorems, 1351 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 76 (borrowed 1, owed 60, structural 15).
registry: 5 borrowed + 99 owed + 39 structural; 67 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
Build completed successfully (3875 jobs).
$ python3 stmts.py     # target 1 against `h3` of the merged `emn2Exp_of_far3`; its conclusion against the pin body
emn2Exp_far3 statement vs `h3` of emn2Exp_of_far3 (EMn2Exp1.lean:1716-1734), whitespace removed: True
conclusion of emn2Exp_of_far3 vs body of STEMn2Exp (Step2Defs.lean:456-475), whitespace removed: True
$ sed -n '884p;896,905p;1090,1091p' RBM3D/Induction/EMn2Exp2.lean     # targets 1, 2 (premise lines 886-895 = `Step2Defs.lean:457-467`, by the script)
theorem emn2Exp_far3 (d : ℕ) (hd : 3 ≤ d) :
                Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                  (fun n p ω => if emn2ExpEllDag sz n (t n) <
                      (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) then
                    emn2ExpS3M sz n (STflowE z n) (t n) (ℓ n) p.1 p.2.1 p.2.2 ω else 0)
                  (fun n p ω => (etaT (STflowE z n) (t n))⁻¹ *
                    ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) +
                      (STJhat sz n (STflowE z n) D (ℓ n) (t n) ω) ^ 3) *
                    (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ _hΨ _hI ℓ hℓ hA D hD
  classical
theorem stEMn2Exp_holds (d : ℕ) (hd : 3 ≤ d) : STEMn2Exp d :=
  emn2Exp_of_far3 d (emn2Exp_far3 d hd)
```

### b.2 Compiled nonempty instances (same file, namespace `RBM.Gauss.EMn2Exp2Inst`)
```
$ python3 inst_list.py     # line, docstring heading of each `example`
1141: **`emn2Exp2_loop6_le`** at the instance matrix: the cut-`0` 6-loop at the four distinct labels `a = 0`, `
1183: **`emn2Exp2_S3_le`** at the instance matrix, for `ℓ* = 0`, `ℓ = 1`, `a = 0`, `b = (1,1,1)` (`|a - b| = 1 
1227: **`emn2Exp2_loop2_far_le`** (`(eq_L2-J)`) at `sz0`, `t ≡ 1/16`, `D = 1`, `ℓ_n = ℓ_t`: eventually, for eve
1252: **`emn2Exp_far3`** (`S̃₃` in the far case `|a - b| > ℓ†_t`, the hypothesis `h3` of `emn2Exp_of_far3`) at 
1273: **`stEMn2Exp_holds`** (the pin `STEMn2Exp 3`, `(eq:MG_conclusion3)`) at the same data: for both cuts, all
1291: **The downstream pin fits**: `STEMn2Exp d` is discharged in `ST_step2_of_pins'` by `stEMn2Exp_holds` (the
```
Data: matrix level `d=3, L=3, W=2`, `H_ij=(i)_0+(j)_0`, `z=1/2+i/4`, `a=0`, `b=(1,1,1)`, `ilambda=1/8`, `t=1/16`, `ℓ=1`, `D=1`, `ℓ*=0`, `y=16`, `F=16²` (envelope `‖𝓛²‖ ≤ η⁻² = 16 ≤ 16² P`, `P ≥ 1/16`), `(TTT2)` and `C_R` from `ekPropTInf_holds 3`, `emn2Exp2_exists_CR 3`.  Model level `sz0`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z0` (`flow_z0`), `t≡1/16`, `ε₀=1/20`, `Ψ=W^{-1}`, `ℓ_n=ℓ_t`, every `D>0`, `3 ≤ d` by `norm_num`.  Every deterministic hypothesis is discharged; `hI : STInitialGT2` and `hA : ∀ D, STLWassmExp` stay hypotheses of the two endpoint examples (other gates' pins; limit checks: T2109 (b.3), (a′) `s3split.py`).  The last example plugs `stEMn2Exp_holds` into `ST_step2_of_pins'`.

### b.3 Name clashes, hygiene, scope, registry pre-check
```
$ grep -rnE "emn2Exp2_|emn2Exp_far3|stEMn2Exp_holds" <RBM3D tree minus the file | main | ../RBM1D/RBM1D ../RBM2D/RBM2D> | wc -l     # 3 greps
0 / 0 / 0
$ grep -nEw "sorry|admit|axiom|native_decide|sorryAx" RBM3D/Induction/EMn2Exp2.lean | wc -l
0
$ git diff main...t/T2118 --stat | tail -3
 RBM3D/Induction/EMn2Exp2.lean | 1295 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    1 -
 2 files changed, 1295 insertions(+), 1 deletion(-)
```
Registry pre-check (full `lake build`; logs `v0.log`-`v2.log`, variant 3 from the tool output; at `aa6e061`, before T2125 changed the registry):
```
variant                                               build theorems  premises found (owed)  registry owed
0 main, root without the module                        ok    3873     79 (62)                101
1 root with the module, registry line kept             ok    3878     78 (61)                101  (STEMn2Exp: "carries nothing")
2 root with the module, line removed (committed)       ok    3878     78 (61)                100
3 line removed, root WITHOUT the module                fail  —        error: [RBM.Gauss.Sizes.STEMn2Exp] is in none of the three lists
```
Ports: none from RBM1D/RBM2D (no diff-stat).  Private declarations of merged RBM3D files are reached with `open private … from` (20 names: 7 of `EMn2Exp1`, 10 of `EMn2Poly`, `card_ball_le` of `ContractPt`, `pti_sum_radial` of `PropTInf`, `KLWard_mSigma_mul` of `KLWard`; precedent `Loop/KLIndStepA.lean:40`).  Copied, because the sources are private and fixed to other regions or not imported: `emn2Exp2_partF` (`emn2Exp_part1`, `EMn2Exp1.lean:502-594`, region `A^f` in place of its `hK`), `emn2Exp2_STKloop_two` (`nkl_STKloop_eq`, `NewKLK.lean:690`, outside the import closure), the instance data `exH …` (`EMn2Exp1Inst`).

### b.4 Narrative
1. Route (ticket Amend 1, DECISIONS §35).  `emn2Exp2_S3_le` splits the region `R₃` of `emn2ExpS3` by `P(|c'-b|) ≤ P(|a-b|)` (`A^f`) or `>` (`A^n`).  `A^f`: `emn2Exp2_partF` = `emn2Exp_part1` with that region, `M = y²P(r)`, `K = 1` (`stContractPt_holds`, `emn2Poly_norm_loop4_alt_le`, `emn2Exp_loop3_ctrl`): `3^d η⁻¹ y⁵ √P(0) P(r)²`; no sum over `c`, no `Ĵ`, no condition on `D`.  `A^n`: `emn2Exp2_loop6_le` (`𝓛⁶ = W^{-6d}‖Y₁Y₂Y₃‖²_HS`, `Y_i` block pieces of `G`, so `|𝓛⁶| ≤ |𝓛²_{(a,c)}||𝓛²_{(b,a)}||𝓛²_{(c',b)}|`; no entry bound) and `emn2Exp2_partN`; on `A^n` the `(c',b)` leg is the tail `W^{-d}𝒯(|c'-b|)` (`P ≥ W^{-d-D}`), so `emn2Exp2_profile_sum` needs only `(TTT2)` and `Σ_c 𝒯_t(|c-b|_∞) ≤ C_R/(1-t)` (`emn2Exp2_sum_tailT_le`, from `pti_sum_radial`): `3^d K₁ W^{-d}(C_T+C_R)P(r)`, `K₁ = 2^{d-2}e` (`emn2Exp2_tailT_shift1` from `emn2Exp_tailT_shift`); the floor-floor term `W^{-2D}Σ_c 1` never occurs.
2. `(eq_L2-J)` = `emn2Exp2_loop2_far_le`: `𝓛² = (𝓛-𝒦) + 𝒦`, `‖𝒦²‖ = W^{-d}‖Θ_t‖ ≤ W^{-d}W^{-(D+d)} ≤ W^{-d}P` beyond `ℓ*`, so every 2-loop at distance `> ℓ*` is `≤ (Ĵ + W^{-d})P`; the far field is `emn2Exp_kellStar_far` (`δ=1`, `D_K=D+d`, `Λ=𝔡⁻¹`, range `ε/2`; `RangeCond` and `t<1` from `Green.v3_premises_of_stFlow`, the `lam` window from `WO`).
3. `emn2Exp_far3`: good event of `hA D hD` at `τ/5` (`emn2Exp_stochDomAt_of_subset`, as in `emn2Exp_far12`), `y = N^{τ/10}`, `F = Ĵ + W^{-d}`, `(TTT2)` from `ekPropTInf_holds` at `u = t` (regime clause `le_total`), `(1-t)⁻¹ ≤ η⁻¹` (`η = (1-t)Im m`, `Im m ≤ 1`), `(Ĵ+w)³ ≤ 4(Ĵ³+w³)`, and the eventual facts `1 ≤ log W`, `W^{-5d} ≤ cB` (so `W^{-3d} ≤ Bctl^{1/2}`), `2(A₁+A₂+1) ≤ N^{τ/2}` with `A₁ = 3^d√(1+cB⁻¹)`, `A₂ = 4·3^d K₁(C_I+C_R)` (`d`, `𝔡` only); the real-number assembly is `emn2Exp2_assemble`.  `stEMn2Exp_holds := emn2Exp_of_far3 d (emn2Exp_far3 d hd)`.
4. DECISIONS §29: (1) `0 ≤ t ≤ lemT z` only for `η>0`, `t<1`, `ST_Bdata_holds`; (2) no regime split (the far set may be empty: nothing to prove); (3) no `L^d ≤ W^K` (only `Bandwidth` of `STFlow`); (4) `Prec` eventual, constants `3^d, K₁, C_I, C_R, √(1+cB⁻¹), 4` free of `W, L, λ, D`.  No new external hypothesis; `ε₀, Ψ`, its window, `STInitialGT2` and the upper bound on `ℓ` are unused, `hA` only at the pin's `D`.  No `(GijGEX)`.

## (c) Verified names (all used by the compiled module; signatures by `#check`, `names2.lean`)
- `Finset.sum_mul_sq_le_sq_mul_sq (s f g) : (∑ f*g)^2 ≤ (∑ f^2) * ∑ g^2`; `Finset.card_le_card_of_injOn (f) : MapsTo → InjOn → #s ≤ #t`; `Finset.le_sup' (f) (h : b ∈ s) : f b ≤ s.sup' _ f`; `Equiv.sum_comp (e) (g) : ∑ g (e i) = ∑ g i`; `Equiv.subRight`; `Complex.im_le_norm : z.im ≤ ‖z‖`; `Real.sqrt_le_one : √x ≤ 1 ↔ x ≤ 1`; `Real.sqrt_eq_rpow`; `Real.rpow_neg_one`; `Real.rpow_le_rpow_of_exponent_le : 1 ≤ x → y ≤ z → x^y ≤ x^z`
- `inv_anti₀ : 0 < b → b ≤ a → a⁻¹ ≤ b⁻¹`; `inv_le_comm₀ : 0 < a → 0 < b → (a⁻¹ ≤ b ↔ b⁻¹ ≤ a)`; `inv_le_one_of_one_le₀`; `pow_le_of_le_one : 0 ≤ a → a ≤ 1 → n ≠ 0 → a^n ≤ a`; `le_self_pow₀ : 1 ≤ a → n ≠ 0 → a ≤ a^n`; `one_le_pow₀`; `mul_le_of_le_one_right : 0 ≤ a → b ≤ 1 → a*b ≤ a`; `le_mul_of_one_le_right : 0 ≤ a → 1 ≤ b → a ≤ a*b`; `max_le_add_of_nonneg : 0 ≤ a → 0 ≤ b → max a b ≤ a + b`; `div_le_iff₀ : 0 < c → (b/c ≤ a ↔ b ≤ a*c)`; `le_or_gt`; `ite_eq_left : c → ite c t e = t`, `ite_eq_right : ¬c → ite c t e = e` (replace the deprecated `if_pos`, `if_neg`)
- RBM3D: `Green.v3_premises_of_stFlow`, `ST_Bdata_holds`, `ST_prof_le_Bctl`, `ST_size_pow_big`, `ST_W_tendsto`, `ST_flow_im_pos`, `ST_STprof_pos`, `ST_JhatM_nonneg`, `emn2Exp_kellStar_far`, `emn2Exp_of_far3`, `ekPropTInf_holds`, `stContractPt_holds`, `emn2Poly_norm_loop4_alt_le`, `rpow_neg_le_tailW`, `tailW_pos`, `tailT_antitone`, `tailT_natCast`, `sum_one_torus`, `inv_mul_ellT_sq_le`, `radC_pos`, `KLK_two`, `norm_loopM_le`, `norm_mE`, `etaT_pos`, `etaT_eq_zt_im`.  Absent: none new (`Real.sqrt_add_le` absent, T2109 (c)).

## (d) Open issues and paper-delta candidates
1. **`3 ≤ d`: decision needed.**  Targets 1-2 are delivered with `(hd : 3 ≤ d)` (see (a″)); the ticket text and the pin have none, and `emn2Exp_far3`, `stEMn2Exp_holds` cannot be proved for `d ∈ {1,2}` from the merged inputs.  The consumers fit as they are: `STStep2 d` is under `3 ≤ d →` (last example of b.2).  Alternatives for the dispatcher: accept (DECISIONS §31 precedent, T2080), or restate `STEMn2Exp` as `3 ≤ d → …` (touches `Step2Defs.lean:456`, `emn2Exp_of_far3` and the theorems listed by `grep -n STEMn2Exp RBM3D/Induction/*.lean`).  No pin was changed.
2. **Registry and merge.**  `Test/Axioms.lean` differs from `main` by the one removed line (`STEMn2Exp`; the branch was rebased on `471b643` after T2125 edited the same file).  The line may be removed only together with the root import of the module (variant 3); if `main`'s file changes before the merge, apply the one-line removal instead of copying the file.
3. `open private` ties this file to private names of five merged files (a rename there breaks the build, not the mathematics); the alternative is copying them, as T2109 did.
4. Paper-delta candidates (proposed tags): **T2118a** (Fable review, DECISIONS §35) `3_5:885-886` (display with `Σ_c[𝒯+W^{-D}][𝒯+W^{-D}]`) needs `D ≥ (d-2) log_W ℓ_t` (the term `W^{-2D}Σ_c 1`); the Lean splits `S̃₃` at `𝒯̃(|c'-b|) ≤ 𝒯̃(|a-b|)`, bounds that part by the contraction inequality as `S̃₁`, so `(eq:MG_conclusion3)` holds for every `D > 0`.  **T2118b** `3 ≤ d` hypothesis of the two theorems (above).  **T2118c** (cf. T2102a, T2109c) `3_5:871, 876` bound the six legs by `(GijGEX)`; the Lean uses the three 2-loops and the Hilbert-Schmidt norm.  **T2118d** `(eq_L2-J)` (`3_5:872-875`): the Lean small term is `W^{-d}` (`D_K = D + d` in the far field of `Θ`), not `W^{-D}`; the last step `(Ĵ+W^{-d})³ ≲ Ĵ³ + (W^{-d}B_{t,0})^{1/2}` holds eventually.  **T2118e** the last `≲ η_t⁻¹` of `3_5:886` is `(1-t)⁻¹ ≤ η_t⁻¹` (`Im m ≤ 1`), no bulk assumption used there.
