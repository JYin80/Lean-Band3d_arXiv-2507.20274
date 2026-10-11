Prover model: claude-sonnet-5-5

# T2401 stage 1a: design gate for BA-G5a (minor good event, minor differences, fluctuation averaging). Mathematics only: no Lean was written; the pins of (G.8) are pseudo-Lean for the Lean-capable compile step.

Citations: `path:N` is relative to `RBM3D/` on `main` (1181514; `BA/GreenCore` merged cbda0ab, `BA/GreenStab` 4a4327e); `7_8:N`, `3_5:N` are lines of `paper/tex/7_8_light_weight.tex`, `3_5_Loop_Hierarchy.tex`. Scripts and verbatim outputs: `docs/reports/T2401/{fa_consts,fa_poly,fa_ident,fa_walk,fa_scale}.py` with `*.out`.
Notation: site `u=(a,o)` (block, offset); `Y_o` = the sites of offset `o`; `N(u)` = the `2d` same-offset neighbours; `Δ=G-M`; `Ψ=2δ`; `R_{β,o}=[β]∖{(β,o)}` (protected rows); `T_{β,o}=Y_o∪[β]`; `s=E+m`, `M=(D-s)⁻¹`, `z=s-tm`.

## (a) Math preflight — Sun Oct 11 02:42:37 UTC 2026
Targets, in mathematics as far as (i)-(ii) need them (names in (G.8)):
- **T1** `o(x)≠o(y) ⇒ M_xy=0`; `|G^{(w)}_xy-G_xy| ≤ (2/κ)|G_xw||G_wy|` when `|G_ww|≥κ/2`.
- **T2** `‖Δ‖_max≤δ`, `κ≤|m|`, `4δ≤κ`, `8m₀δ≤κ` ⇒ for `S⊆R_{β,o}`, `|S|≤m₀`, `x,y∈T_{β,o}∖S`: `|G^{(S)}_xy-M_xy|≤2δ`, `|G^{(S)}_xx|≥κ/2`.
- **T3** bounded polynomial families `Y^A,Y^X` with `A_u=Y^Am/G_uu`, `𝔛_uy=-Y^Xm/G_uu`, base bounds. **T4** `‖Δ_{κ_1…κ_m}Y‖ ≤ c_Y(m)Ψ^{m+1}` on protected rows.
- **T5** `E|Σ_x T_xQ_xY_x|^{2p} ≤ (2p+1)(2p)^{2p}(2^{2p-1}ρB)^{2p}` under the family gain interface, `0≤T≤c≤ρ²`, `ΣT≤1`, `ρ≤1`, `2p≤#A`. **T6** the exact identity for `⟨M𝒦⟩_a`. **T7** the owed pin `BAFAav`.

### (i) Exponent table (`python3 fa_consts.py`; `κ` uniform in `L≥64`, `Λ=𝔡⁻¹=10`, `d=3`)
| # | quantity | value at `g = 1/64 / 1 / 10` | constraint | slack |
|---|---|---|---|---|
| 1 | `κ`; `Im m(z)` (`L=64/96/128`); `Im m₀` | `0.5/0.25/0.04`; `0.8325/0.3435/0.0439`; `0.9995/0.642/0.2095` | `κ ≤ Im m(z)` (`BAdom`), `κ ≤ Im m₀ ≤ |m₀| ≤ 1` | `1.67/1.37/1.10` (vs `Im m`); `2.0/2.6/5.2` (vs `Im m₀`) |
| 2 | `g₀=√t₀ g` (`L→∞`); `|s|` (`E=0` on this family; the pins take `‖s‖`) | `0.0130/0.5350/2.0955`; `0.9995/0.642/0.2095` | `0<g₀≤Λ=10` (`BAflow_lam0_window`, `GreenSchur.lean:72`) | `770/18.7/4.8` |
| 3 | `2d g₀` (`=Σ_l‖D_ul‖`, `GreenCore_Drow` `:672`) | `0.078/3.21/12.57`, worst `2dΛ=60` | enters only `K_Y, K'_Y` | `L`-, `W`-free |
| 4 | smallness `δ` (T2): `4δ≤κ`; `8Mδ≤κ`, `M=2p` | `δ≤0.125/0.0625/0.01`; `p=1`: `0.0312/0.0156/0.0025`; `p=2`: `0.0156/0.0078/0.00125` | hypotheses of T2, T4; eventual in `n` (`δ=W^{τ}Ψ≤W^{τ-ε₀}`) | at `W=2^{24}, ε₀=1`: `4.2e4` at `g=10` (row 8) |
| 5 | window `Ψ∈[W^{-d/2}, W^{-ε₀}]` | `[1.46e-11, 5.96e-8]` at `W=2^{24}`, `ε₀=1` | nonempty iff `ε₀≤d/2=3/2` | `W^{1/2}=4096`; `ε₀=3/2`: equality |
| 6 | weights `c=W^{-d} ≤ ρ²`, `ρ=4δ` | `2.1e-22 ≤ 5.7e-14` (`W=2^{24}, ε₀=1`) | `T≤c≤ρ²`, `ρ≤1`, `2p≤W^d` | `2.7e8`; at `ε₀=3/2` (`δ=Ψ=W^{-3/2}`) `ρ²=16c` |
| 7 | moments `F_p=(2p+1)(2p)^{2p}2^{(2p-1)2p}`, `M=K=2p`; `p=⌈(D+2/𝔠+1)/(2τ)⌉` | `F_1=48`, `F_2=5.2e6`, `F_3=3.5e14`; `τ=0.1, D=10`: `p=55` (`𝔠`-free part) | `P(|avg|>W^τρB)≤F_pW^{-2pτ}`; union over `≤N²` pairs, `N≤W^{1/𝔠}` | `p` fixed before `n` |
| 8 | atom constants. Route A (band recursion, `a_0=2/κ`, `a_{r+1}=16^ra_r^5`); Route B (walk expansion, `c_1=q=2/κ`, `c_m=2m(m-1)^{m-1}q^m`) | `log₁₀a_1,a_2`: `3.0,16.3 / 4.5,23.8 / 8.5,43.7`; `c_2=64/256/10⁴` | grading `‖Δ^mY‖≤c_Y(m)Ψ^{m+1}`, `c_Y=K_Yc_m+K'_YP_mΨ`, `K_Y=(‖s‖+2dg₀)(1/κ+1)`, `K'_Y=4dg₀/κ` | `K_Y=3.2/19.3/332` |
| 9 | `hB1` (G5b, band form `4C_2δ+2δ≤1`): `W` needed at `ε₀=1` (`3/2`) | A: `10^{33.2}/10^{50.2}/10^{91.4}` (`10^{22.1}/10^{33.5}/10^{60.9}`); B: `8.3e2/2.0e4/1.3e7` (`88/730/5.6e4`) | eventual in `n` only (as T2390 R2) | B at `W=2^{24}`: `2e4/850/1.26` |
| 10 | `ρ_row=sup_aΣ_b|M_ab|`; `ρ₂=sup Σ_b|M_ab||M_bc|`; `K_Θ=16κ⁻⁴` | obs. `1.08/15.9/447`; analytic `4.9e15/1.6e17/1.5e21`; `ρ₂≤1`; `K_Θ=256/4096/6.25e6` | `BAMB_row_l1` `:139`, `baM_rho2`, `baStab_of_real` (`GreenStab:46`) | `L`-uniform |
| 11 | final exponent: `|⟨M𝒦⟩_a| ≤ C_*δ_n²`, `δ_n=W^{τ}Ψ_n` | `W^{2τ}Ψ²≺Ψ²` | `τ<ε₀` arbitrary; `δ_n≤δ*` eventually | none lost |
| 12 | C1/G2: where `g` enters | only `g₀≤Λ` in `K_Y,K'_Y` and `ρ_row` | no `g≤W^{-ε}`, no `‖M-m₀I‖` small, no `(Cλ)^{|a-b|}`, no `c_λ`, no `K_BA` | — |

### (ii) One concrete nondegenerate instance
Deterministic targets T1-T4, T6: `d=3, L=3, W=2` (`N=216`, `W^d=8` offsets), flow data `(g₀,E,m₀)` of the three `g`, `t=0.9·10⁻⁵·t₀`, `G=(D+X-z)⁻¹` for the sampled in-block GUE `X≠0`, `D=g₀Ψ≠0`: every hypothesis (`M` Kronecker, `(D-s)M=1`, `z=s-tm`, `‖Δ‖_max=δ₀≈10⁻³`, `4δ₀≤κ`, `16δ₀≤κ`) holds and is read off the output; T2 is checked by `(I5)`, T4 by `(P3)`. T5 at the same `d, W`: `#A=8`, `T=1/8`, `c=1/8≤ρ²=1/4`, `ρ=1/2`, `2p=2≤8`; the gain interface `famGain` stays a hypothesis (G5b's pin). T7 is a pin (hypothesis `BAGiiGEX`, G6's). No external hypothesis (nothing is cited from `[RBSO1D]`); the asymptotic numbers (rows 5-9) are at `W=2^{24}`.
```
$ cd docs/reports/T2401 && python3 fa_consts.py | sed -n '1,2p;4p;6p;12p;16p;20p;24,26p;37,42p;45p'     (flow data; Route A, Route B; instances)
g | L | kappa | Im m(z) | Im z | t0 | g0 | |m0| | Im m0 | |s| | 2d g0 | 2d Lam | c=BAct_rate | rho_row obs
0.015625 | 64 | 0.5 | 0.8325 | 0.368 | 0.6937 | 0.0130 | 0.9995 | 0.9995 | 0.9995 | 0.078 | 60 | 4.158e-03 | 1.08   [BAdom Im m>=kappa, Im z<=1, kappa<=Im m0, |m0|<=1, g0<=Lam: True]
1 | 96 | 0.25 | 0.3435 | 0.857 | 0.2862 | 0.5350 | 0.6420 | 0.6420 | 0.6420 | 3.210 | 60 | 2.081e-03 | 15.91   [BAdom Im m>=kappa, Im z<=1, kappa<=Im m0, |m0|<=1, g0<=Lam: True]
10 | 128 | 0.04 | 0.0439 | 0.956 | 0.0439 | 2.0955 | 0.2095 | 0.2095 | 0.2095 | 12.573 | 60 | 3.333e-04 | 447.21   [BAdom Im m>=kappa, Im z<=1, kappa<=Im m0, |m0|<=1, g0<=Lam: True]
   [g0 = flow] K_Y = 3.23, K'_Y = 0.31; log10 c_Y(0..3) = 1.3 5.8 32.6 167.8;  log10 C_2 = 32.6;  hB1 needs delta <= 10^-33.2  => W >= 10^33.2 at eps0 = 1,  10^22.1 at eps0 = 3/2
   [g0 = flow] K_Y = 19.26, K'_Y = 25.68; log10 c_Y(0..3) = 3.3 10.7 49.6 244.9;  log10 C_2 = 49.6;  hB1 needs delta <= 10^-50.2  => W >= 10^50.2 at eps0 = 1,  10^33.5 at eps0 = 3/2
   [g0 = flow] K_Y = 332.34, K'_Y = 628.64; log10 c_Y(0..3) = 6.2 20.1 90.8 445.3;  log10 C_2 = 90.8;  hB1 needs delta <= 10^-91.4  => W >= 10^91.4 at eps0 = 1,  10^60.9 at eps0 = 3/2
g = 0.015625, kappa = 0.5: q = 4.0; c_m = 1 4 64 1.54e+03; c^B_Y(0..2) = 3.23 12.9 207; C_2 = 2.070e+02; delta* = 1.205e-03; 4 delta* <= kappa: True; 16 delta* <= kappa: True; W >= 8.30e+02 at eps0 = 1, 8.83e+01 at eps0 = 3/2
g = 1, kappa = 0.25: q = 8.0; c_m = 1 8 256 1.23e+04; c^B_Y(0..2) = 19.3 154 4.93e+03; C_2 = 4.932e+03; delta* = 5.068e-05; 4 delta* <= kappa: True; 16 delta* <= kappa: True; W >= 1.97e+04 at eps0 = 1, 7.30e+02 at eps0 = 3/2
g = 10, kappa = 0.04: q = 50.0; c_m = 1 50 1e+04 3e+06; c^B_Y(0..2) = 332 1.66e+04 3.32e+06; C_2 = 3.323e+06; delta* = 7.522e-08; 4 delta* <= kappa: True; 16 delta* <= kappa: True; W >= 1.33e+07 at eps0 = 1, 5.61e+04 at eps0 = 3/2
parameter instance d = 3, W = 2^24 = 16777216, eps0 = 1, delta = W^-eps0 = 5.960e-08, Psi = 2 delta, rho = 4 delta, c = W^-d, p = 1 (M = K = 2)
  window [W^-d/2, W^-eps0] = [1.455e-11, 5.960e-08] nonempty: True (ratio 4096);  c = 2.118e-22 <= rho^2 = 5.684e-14: True (slack 2.68e+08); rho <= 1: True; 2p = 2 <= #A = W^d
  g = 0.015625, kappa = 0.5: 4 delta = 2.38e-07 <= kappa: True; 8 M delta = 9.54e-07 <= kappa: True (slack 5.24e+05); hB1 (Route B, band form) 4 C_2 delta + 2 delta = 0.000 <= 1: True (slack 20211.83)
  g = 1, kappa = 0.25: 4 delta = 2.38e-07 <= kappa: True; 8 M delta = 9.54e-07 <= kappa: True (slack 2.62e+05); hB1 (Route B, band form) 4 C_2 delta + 2 delta = 0.001 <= 1: True (slack 850.31)
  g = 10, kappa = 0.04: 4 delta = 2.38e-07 <= kappa: True; 8 M delta = 9.54e-07 <= kappa: True (slack 4.19e+04); hB1 (Route B, band form) 4 C_2 delta + 2 delta = 0.792 <= 1: True (slack 1.26)
  eps0 = 3/2 (floor): c <= rho^2  <=>  W^(3 - 2 eps0) >= 1/16: slack 16 (W^0 = 1)
Lean-size instance of the moment bound (same d = 3, W = 2 as the sample): #A = W^d = 8, T = W^-d on A (c = 0.125), sum T = 1.0, rho = 0.5 <= 1, c <= rho^2 = 0.25: True, 2p = 2 <= #A: True, M = K = 2p; bound (2p+1)(2p)^(2p)(2^(2p-1) rho B)^(2p) = 3.0
$ python3 fa_poly.py 1e-5 | cut -c1-262 | grep -v "^(P5)" ; python3 fa_poly.py 1e-5 | grep "^(P5)" | cut -c1-175      (d=3, L=3, W=2 sample, t = 0.9e-5 t0)
--- g = 0.015625, t = 6.244e-06 (t_scale 1e-05), |m0| = 0.9995, |s| = 0.9995, g0 = 0.0130, delta0 = ||G-M||_max = 2.890e-03, min|G_uu| = 0.999
(P1) max|A_u - YA m0/G_uu| = 5.1e-16; max|XX_uy + YX m0/G_uu| = 2.0e-17; max|A_u - YA|/delta0^2 = 1.00; max|XX_uy + YX|/delta0^2 = 0.19
(P2) max|YA|/delta0 = 1.001 <= C_A = 1.078: True;  max|YX|/delta0 = 0.503 <= C_X = 2.156: True
(P3) |Delta^m Y|/delta0^(m+1), m = 0..3:  YA: 0.36 0.29 0.12 0.03 | YX: 0.00 0.00 0.00 0.00 | YX negative control (first removed row = offset o in another block): 0.00 0.00 0.00
(P4) max |G^(w)_xy - G_xy| / ((2/kappa) delta0 |G_wy|) = 0.707 (o(x) != o(w));  max |G^(w)_xy - G_xy| / ((2/kappa) delta0^2) = 0.117 (also o(w) != o(y)); kappa(lemma) = 2(|m0| - delta0) = 1.993
--- g = 1, t = 3.234e-06 (t_scale 1e-05), |m0| = 0.7198, |s| = 0.7193, g0 = 0.5994, delta0 = ||G-M||_max = 1.065e-03, min|G_uu| = 0.720
(P1) max|A_u - YA m0/G_uu| = 1.1e-15; max|XX_uy + YX m0/G_uu| = 6.1e-16; max|A_u - YA|/delta0^2 = 2.72; max|XX_uy + YX|/delta0^2 = 0.41
(P2) max|YA|/delta0 = 1.955 <= C_A = 5.996: True;  max|YX|/delta0 = 0.707 <= C_X = 10.323: True
(P3) |Delta^m Y|/delta0^(m+1), m = 0..3:  YA: 0.70 0.81 0.47 0.21 | YX: 0.00 0.06 0.07 0.03 | YX negative control (first removed row = offset o in another block): 0.03 11.10 9.56
(P4) max |G^(w)_xy - G_xy| / ((2/kappa) delta0 |G_wy|) = 0.693 (o(x) != o(w));  max |G^(w)_xy - G_xy| / ((2/kappa) delta0^2) = 0.140 (also o(w) != o(y)); kappa(lemma) = 2(|m0| - delta0) = 1.437
--- g = 10, t = 4.005e-06 (t_scale 1e-05), |m0| = 0.6671, |s| = 0.6671, g0 = 6.6711, delta0 = ||G-M||_max = 9.782e-04, min|G_uu| = 0.667
(P1) max|A_u - YA m0/G_uu| = 4.3e-15; max|XX_uy + YX m0/G_uu| = 7.5e-15; max|A_u - YA|/delta0^2 = 3.55; max|XX_uy + YX|/delta0^2 = 0.61
(P2) max|YA|/delta0 = 2.368 <= C_A = 60.999: True;  max|YX|/delta0 = 0.794 <= C_X = 101.810: True
(P3) |Delta^m Y|/delta0^(m+1), m = 0..3:  YA: 0.85 1.15 0.87 0.35 | YX: 0.00 0.11 0.12 0.05 | YX negative control (first removed row = offset o in another block): 0.06 26.82 25.24
(P4) max |G^(w)_xy - G_xy| / ((2/kappa) delta0 |G_wy|) = 0.724 (o(x) != o(w));  max |G^(w)_xy - G_xy| / ((2/kappa) delta0^2) = 0.185 (also o(w) != o(y)); kappa(lemma) = 2(|m0| - delta0) = 1.332
(P5) max_a |<MK>_a - (vbar_a - t sum_b M_ab M_ba vbar_b)| = 4.5e-16;  max_a |T1+T2+T3+T4 - <MK>_a| = 3.3e-19;  max_a |T1|,|T2|,|T3|,|T4| / delta0^2 = 0.00 83.48 0.21 0.00;  ma
(P5) max_a |<MK>_a - (vbar_a - t sum_b M_ab M_ba vbar_b)| = 5.4e-16;  max_a |T1+T2+T3+T4 - <MK>_a| = 8.1e-20;  max_a |T1|,|T2|,|T3|,|T4| / delta0^2 = 0.00 232.08 0.35 0.07;  m
(P5) max_a |<MK>_a - (vbar_a - t sum_b M_ab M_ba vbar_b)| = 1.5e-15;  max_a |T1+T2+T3+T4 - <MK>_a| = 2.2e-19;  max_a |T1|,|T2|,|T3|,|T4| / delta0^2 = 0.00 287.64 0.52 0.14;  ma
$ python3 fa_ident.py | grep "^(I5)" | awk 'NR%3==0' | cut -c1-300       (minor recursion `δ_{j+1}=δ_j+δ_j²/(|m|-δ_j)` against direct minors, `S⊆R_{β,o}`, `x,y∈T_{β,o}∖S`, j=0..3, g=1/64,1,10)
(I5) t=6.2e-05 delta_0=9.137e-03:  max|g_S - M| on T\S, |S|=j: 9.14e-03 9.14e-03 9.14e-03 8.14e-03   recursion bound: 9.14e-03 9.22e-03 9.31e-03 9.40e-03   all within: True
(I5) t=3.2e-05 delta_0=3.366e-03:  max|g_S - M| on T\S, |S|=j: 3.37e-03 3.37e-03 3.37e-03 3.14e-03   recursion bound: 3.37e-03 3.38e-03 3.40e-03 3.41e-03   all within: True
(I5) t=4.0e-05 delta_0=3.093e-03:  max|g_S - M| on T\S, |S|=j: 3.09e-03 3.09e-03 3.09e-03 2.99e-03   recursion bound: 3.09e-03 3.11e-03 3.12e-03 3.14e-03   all within: True
$ python3 fa_walk.py | cut -c1-330      (walk expansion: m-fold difference of one entry, atoms in T, protected rows)
g = 0.015625: Psi = 2.890e-03, q = 1/(|m0| - Psi) = 1.003;  m = 1: |direct - walk sum (<= 6 vertices)|/(c_m Psi^(m+1)) = 3.6e-14, max |Delta^m G_ab|/(c_m Psi^(m+1)) = 0.000;  m = 2: |direct - walk sum (<= 6 vertices)|/(c_m Psi^(m+1)) = 4.2e-09, max |Delta^m G_ab|/(c_m Psi^(m+1)) = 0.003;  m = 3: |direct - walk sum (<= 6 vertices)|/(c_m Psi^(m+1)) = 3.2e-10, max |Delta^m G_ab|/(c_m Psi^(m+1)) = 0.000;
g = 1: Psi = 1.065e-03, q = 1/(|m0| - Psi) = 1.391;  m = 1: |direct - walk sum (<= 6 vertices)|/(c_m Psi^(m+1)) = 2.6e-10, max |Delta^m G_ab|/(c_m Psi^(m+1)) = 0.036;  m = 2: |direct - walk sum (<= 6 vertices)|/(c_m Psi^(m+1)) = 5.3e-08, max |Delta^m G_ab|/(c_m Psi^(m+1)) = 0.005;  m = 3: |direct - walk sum (<= 6 vertices)|/(c_m Psi^(m+1)) = 5.0e-06, max |Delta^m G_ab|/(c_m Psi^(m+1)) = 0.000;
g = 10: Psi = 9.782e-04, q = 1/(|m0| - Psi) = 1.501;  m = 1: |direct - walk sum (<= 6 vertices)|/(c_m Psi^(m+1)) = 1.3e-09, max |Delta^m G_ab|/(c_m Psi^(m+1)) = 0.047;  m = 2: |direct - walk sum (<= 6 vertices)|/(c_m Psi^(m+1)) = 1.2e-07, max |Delta^m G_ab|/(c_m Psi^(m+1)) = 0.008;  m = 3: |direct - walk sum (<= 6 vertices)|/(c_m Psi^(m+1)) = 1.1e-05, max |Delta^m G_ab|/(c_m Psi^(m+1)) = 0.000;
$ grep -E "^---|ns=   8|ns= 128" fa_scale.out | cut -c1-250      (offset averages vs one term, ring of 4 blocks, `t=0.5`, `g₀=1/64,1,4.67`, `ns=W^d` offsets; seeded Monte Carlo)
--- g0 = 0.015625, L = 4, t = 0.5 ---
ns=   8 samples= 800 Im m0=1.000  RMS|XX_o|=5.260e-03 RMS|avg XX|=1.835e-03 ratio*sqrt(ns)=0.99   RMS|A'_o|=3.721e-01 RMS|avg A'|=1.763e-01 ratio*sqrt(ns)=1.34   RMS|Delta_cross|=3.541e-01  avg XX / cross^2 = 0.01  RMS|Delta_cross|*sqrt(ns) = 1.001  
ns= 128 samples=  60 Im m0=1.000  RMS|XX_o|=1.376e-03 RMS|avg XX|=1.232e-04 ratio*sqrt(ns)=1.01   RMS|A'_o|=8.732e-02 RMS|avg A'|=1.092e-02 ratio*sqrt(ns)=1.41   RMS|Delta_cross|=8.831e-02  avg XX / cross^2 = 0.02  RMS|Delta_cross|*sqrt(ns) = 0.999  
--- g0 = 1, L = 4, t = 0.5 ---
ns=   8 samples= 800 Im m0=0.749  RMS|XX_o|=8.536e-02 RMS|avg XX|=2.982e-02 ratio*sqrt(ns)=0.99   RMS|A'_o|=3.343e-01 RMS|avg A'|=1.433e-01 ratio*sqrt(ns)=1.21   RMS|Delta_cross|=2.251e-01  avg XX / cross^2 = 0.59  RMS|Delta_cross|*sqrt(ns) = 0.637  
ns= 128 samples=  60 Im m0=0.749  RMS|XX_o|=2.227e-02 RMS|avg XX|=2.048e-03 ratio*sqrt(ns)=1.04   RMS|A'_o|=8.042e-02 RMS|avg A'|=7.891e-03 ratio*sqrt(ns)=1.11   RMS|Delta_cross|=5.616e-02  avg XX / cross^2 = 0.65  RMS|Delta_cross|*sqrt(ns) = 0.635  
--- g0 = 4.6723, L = 4, t = 0.5 ---
ns=   8 samples= 800 Im m0=0.709  RMS|XX_o|=2.516e-02 RMS|avg XX|=8.841e-03 ratio*sqrt(ns)=0.99   RMS|A'_o|=3.572e-01 RMS|avg A'|=1.516e-01 ratio*sqrt(ns)=1.20   RMS|Delta_cross|=2.481e-01  avg XX / cross^2 = 0.14  RMS|Delta_cross|*sqrt(ns) = 0.702  
ns= 128 samples=  60 Im m0=0.709  RMS|XX_o|=6.506e-03 RMS|avg XX|=6.071e-04 ratio*sqrt(ns)=1.06   RMS|A'_o|=8.628e-02 RMS|avg A'|=8.382e-03 ratio*sqrt(ns)=1.10   RMS|Delta_cross|=6.197e-02  avg XX / cross^2 = 0.16  RMS|Delta_cross|*sqrt(ns) = 0.701
```
(Reading: `(P3)` protected rows `≤1.15` against `25-27` for the control row of the protected offset in another block; `(P4)`, `(I5)` within their bounds; `(P5)` exact to `1e-15`; `fa_scale`: `ratio·√ns ≈ 1.0` for `𝔛` and `1.1-1.4` for `A'` at `ns=8…128`, i.e. the offset average gains `W^{-d/2}`; the `(P5)` magnitudes at `W=2` are not an `O(Ψ²)` test: the window `Ψ≥W^{-d/2}` fails there.)

### Verdicts of section (a)
**T1 PASS, T2 PASS, T3 PASS, T4 PASS** (Route A as pinned; Route B optional), **T5 PASS, T6 PASS, T7 PASS** (pin). **(iv) closes**: no REQ. Hypothesis sets nonempty at the numbers above; the exponents close eventually in `n` (rows 4-9, 11); the only cost is the analytic constants (row 9), as in T2390 R2.

## (G) Design gate: the BA argument for G5a (C1: only uniform facts)

### G.1 Merged facts used (file:line, all present on `main`)
`BAMfine_eq` `BA/GreenSchur.lean:93` (`M_xy=1_{o(x)=o(y)}M^B_{[x][y]}`), `BAMfine_norm_le_one` `:105`, `BAMB_row_l1` `:139`, `BAPsiI_inBlock` `:265`, `baStab_of_real` `BA/GreenStab.lean:46`, `baM_rho2` `:132`. `BA/GreenCore.lean`: `GreenCore_m1` `:400` (m1), `GreenCore_Xrow` `:382`, `GreenCore_Arow` `:390`, `GreenCore_eps1/2` `:551/:555`, `GreenCore_Qxd` `:559`, `GreenCore_Bsum` `:619`, `GreenCore_Arow_eq` `:651`, `GreenCore_Drow` `:672`, `GreenCore_K` `:1248`, `GreenCore_E3` `:1253`, `BAStab` `:1268`, `GreenCore_coupled` `:1276`, carrier abbrevs `:1520-1526`. `BA/GreenLDE.lean:199` (`baLDEin_holds`). Band: `GoodEvent` `Green/EntryCore.lean:406`, `greenMinor` `:280`; `greenSetMat` `Green/MinorGoodLe.lean:261`, `gEnt` `:326`, `applyOps_eq_applyOps_minorDiff` `:439`, `greenSetMat_insert_apply` `:572`, `MinorGoodLe` `:943`, `minorGoodLe_of_goodEvent` `:977`; `deltaFam` `Green/MinorDiff.lean:103`, `DiffBd` `:224`, `DiffBd.delta/.mul` `:283/:318`, `atomC` `:529`, `diffBd_atom` `:570`; `OpsOk/OpsOkOut` `Green/FlucIter.lean:603/:610`; `norm_integral_prod_applyOps_le_graded` `Green/FlucIterGain.lean:566`, `FlucGainUpTo'` `:727`, `integral_norm_flucAvg_pow_le_iter_budget` `:823`; `BoundedWeight` `Green/FlucVanish.lean:941`, `flucAvg` `:1028`, `uniformWeight_blockAvg2` `:1245`; `minorDiffGainUpTo'_goodEvent` `Green/MinorDiffCond.lean:888`; `RowIndep_submatrix_shift_congr` `Green/RowIndep.lean:1341`. Pins: `BAGiiGEX` `BA/Step1Boot.lean:79`, `BAGavLGEX` `:97`, `BAGbEXPav` `:123`; `STInitialGT2gL` `Chain/Carrier.lean:140`. Paper: `7_8:1916-1948` (the lemma; proof "verbatim [RBSO1D] L6.1", premise `g≤W^{-ε}`, T2378 F2), `3_5:20-34` (`(initialGT2)`, `(GavLGEX)`).

### G.2 (i) The BA good event and the minor identity
- Event `Ω_δ={‖G-M‖_max≤δ}`, `κ≤|m|` (`M_uu=m`), `δ≤κ/2` ⇒ `|G_uu|≥κ/2` (T2390 (a′) D3.1). Minor identity `G^{(w)}_vy=G_vy-G_vwG_wy/G_ww`; (m1) `|G^{(w)}_vy|²≤2|G_vy|²+(8/κ²)|G_vw|²|G_wy|²` is `GreenCore_m1`.
- **BA good event (T2).** `GoodEvent` centres `G_xy` at `0` for all `x≠y`; at BA only the cross-offset entries are centred at `0`, the rest at `M`: `Δ=G-M` is the object, `‖Δ‖_max≤δ` the event. **Protected levels:** only rows of one block and of offset `≠o` are removed (`S⊆R_{β,o}`); the entries read are `x,y∈T_{β,o}`. Reason: removing a site `w` of another block with the offset of `y` moves `G_yy` by `-G_ywG_wy/G_ww`, with `G_yw≈M^B_{[y][w]}=O(g)` (not small); no estimate is claimed for such removals (negative control `(P3)`: `25-27` against `0.11`).
- **Recursion.** For `κ'∈R∖S` and `x,y∈T∖(S∪κ')`: `M_{xκ'}=M_{κ'y}=0` (`x∈Y_o` has offset `o≠o(κ')`; `x∈[β]∖κ'` has another offset), so `G^{(S∪κ')}_xy-M_xy=(G^{(S)}-M)_xy-G^{(S)}_{xκ'}G^{(S)}_{κ'y}/G^{(S)}_{κ'κ'}` and `δ_{j+1}≤δ_j+δ_j²/(|m|-δ_j)`. Under `4δ≤κ`, `8m₀δ≤κ`: `δ_j≤δ+8jδ²/κ≤2δ` for `j≤m₀`, `|G^{(S)}_{κ'κ'}|≥|m|-2δ≥κ/2`. This is `minorGoodLe_of_goodEvent` (`:977`: `Ψ≤1/4`, `8MΨ≤1`) with `|m|=1` replaced by `|m|≥κ`: `4δ≤κ`, `8m₀δ≤κ`. Checked `(I5)` (direct minors against the recursion).

### G.3 (ii) The structural fact, general form (T1)
`o(x)≠o(y) ⇒ M_xy=0 ⇒ G_xy=Δ_xy` (`BAMfine_eq`). Hence `|G^{(w)}_xy-G_xy|=|G_xwG_wy/G_ww|≤(2/κ)|G_xw||G_wy|`, and `|G_xw|≤δ` if `o(x)≠o(w)`, `|G_wy|≤δ` if `o(w)≠o(y)`: the difference is `≤(2/κ)δ|G_wy|`, `≤(2/κ)δ|G_xw|`, or `≤(2/κ)δ²` (both). For `w=u'∈[u]∖u` (offset `≠o(u)`): `o(w)≠o(y)` for `y=(a,o(u))` for every block `a`, and for `y∈N(u)`; and `o(x)≠o(w)` for `x∈[u]`, `x∈N(u)`. Checked `(P4)` (`≤0.72`).

### G.4 (iii) Fluctuation averaging, one block: the reading of T2390 G.3 verified and refined
- **Verified:** every removal difference met is a product of two cross-offset entries, one `Ψ` per removed row (T2390 G.3; `(P3)`).
- **Refinement 1 (the families).** `A_u=tm+X_uu-Q^{XX}_u-Q^{XD}_u` equals `(1+sG_uu-Σ_lD_ulG_lu)/G_uu` (`GreenCore_Arow` with `(YG)_{uu}`; `(P1)`). Its entries include the same-offset neighbours `G_lu`, `l∈N(u)` (blocks `β±e_j`): the family is not "one block" in its entries; the removed rows still are (`R_{β,o}`, one block). With `E_uQ^{XX}=tΣ_kS_{uk}G^{(u)}_{kk}` (Gaussian), `Q_uA_u=X_uu-ε₁-Q^{XD}_u` and `A_u+tv̄=Q_uA_u+ε₂` (`GreenCore_Arow_eq`, `ε₂=tW^{-d}(G_uu+Σ_{k≠u}G_kuG_uk/G_uu)`, `|ε₂|≤W^{-d}(1+δ)+2tδ²/κ`): the fluctuations `(1-E_u)Q^{XX}_u`, `X_uu` and `Q^{XD}_u` of T2390 G.3 are all inside `Q_uA_u`; no separate family (`Q^{XD}_u=g₀Σ_{l∈N(u)}𝔛_{ul}` is the family `Y^X` at `α=β±e_j`).
- **Refinement 2 (boundedness).** The Gaussian forms `𝔛, Q^{XX}` and `1/G_uu` are unbounded; the merged iteration needs `BddMeas` families (`‖G^{(S)}_xy‖≤η⁻¹`). The families of G.5 are polynomials in the entries (no division).

### G.5 (iv) Fluctuation averaging over two blocks: the argument (closes)
**Families (T3).** With `Δ^{(S)}=G^{(S)}-M`, sums over `N(u)` (`D_ul=g₀`):
`Y^A_u=(sΔ_uu-Σ_lD_ulΔ_lu)/m`; `Y^X_{uy}=M_uy(sΔ_uu-Σ_lD_ulΔ_lu)/m+(Σ_lD_ulΔ_ly-sΔ_uy)+(Δ_uuΣ_lD_ulΔ_ly-Δ_uyΣ_lD_ulΔ_lu)/m`.
By `(D-s)M=1` (`Σ_lD_ulM_ly=sM_uy` for `y≠u`, `Σ_lD_ulM_lu=1+sm`): `A_u=Y^Am/G_uu` and `𝔛_uy=-G_uy/G_uu-Σ_lD_ulG^{(u)}_ly=-Y^Xm/G_uu` (`𝔛_uy=Σ_{v∈[u]∖u}X_uvG^{(u)}_vy`; the second form is the row Schur identity `G_uy=-G_uuΣ_{l≠u}H_ulG^{(u)}_ly`, `GreenCore_row_schur` `GreenCore.lean:69`, private, `H=D+X`), exact to `1e-15` (`(P1)`). Base: `|Y^A|≤(‖s‖+2dg₀)δ'/κ`, `|Y^X|≤[(‖s‖+2dg₀)(1/κ+1)+4dg₀δ'/κ]δ'` (`‖M_uy‖≤1`, `δ'` the level bound; `(P2)`). With `G_uu=m+Δ_uu`: `A_u=Y^A-A_uΔ_uu/m`, `𝔛_uy=-Y^X_{uy}-𝔛_uyΔ_uu/m`; since `E_u𝔛_uy=0` (coefficients `G^{(u)}_{vy}` do not read row `u`):
 `𝒜'_u:=A_u+tv̄=Q_uY^A-Q_u[A_uΔ_uu]/m+ε₂`, `𝔛_uy=-Q_uY^X-Q_u[𝔛_uyΔ_uu]/m`. (E)
Both remainders are `O(δ²)` pointwise on `Ω_δ` (`|A_u|≤2‖Y^A‖‖m‖/κ`, `|𝔛|` likewise); `Q_uF=F-E_uF` with `E_uF` controlled by `norm_condRow_le_split` (G5b, item (m5)).
**Gain per removed row (T4).** For `κ_1..κ_m∈R_{β,o}` distinct and an atom `Δ^{(S)}_{ab}`, `a,b∈T∖{κ_i}`: by `(m1)`/(4.9) `Δ_κΔ^{(S)}_{ab}=G_{aκ}G_{κb}/G_{κκ}` with both factors cross-offset (G.3): order `2`. Two routes to the constant:
- **A (zero new proof):** `DiffBd` (`MinorDiff.lean:224`) on the protected levels with the band recursion and `a_0=2/κ` (the inverse-diagonal bound `2` of `inv_le` becomes `2/κ`): `a_{r+1}=16^ra_r^5`. Sums of atoms need a sum rule (absent: `DiffBd` has `.neg, .mul, .delta, .shift` only, `+40` lines).
- **B (sharp, proved here, not pinned):** for `U⊆{κ_i}`, `(g_UU)⁻¹=Σ_{walks}(-1)^k…` (Neumann series, `‖D⁻¹E‖≤(m-1)qΨ≤1/2`), `G^{(S∪U)}_{ab}=g_ab-Σ_{walks⊆U}c(w)` with `c(w)` independent of `U`; inclusion-exclusion keeps the walks covering all `κ_i`: `Δ^mG_ab=(-1)^{m+1}Σ_{w covers}c(w)`, `|·|≤c_mΨ^{m+1}`, `c_1=q`, `c_m=2m(m-1)^{m-1}q^m`, `q=2/κ`. Products (Möbius, `F(U)=Σ_{A⊆U}(-1)^{|A|}Δ_AF`): `|Δ_{[m]}(FG)|≤Σ_{A∪B=[m]}|Δ_AF||Δ_BG|`, so `P_m=Σ_{A∪B=[m]}c_{|A|}c_{|B|}Ψ^{|A|+|B|-m}`, `c_0=1`. Checked `fa_walk` (walk sum against direct minors; ratio `≤0.047`).
`c_Y(m)=K_Yc_m+K'_YP_mΨ` (table row 8); the thresholds of `hB1` fall from `10^{33-91}` (A) to `10^{3-7}` (B). The Lean pin states Route A constants (`GreenMinor_cY`); B is an optional primed successor.
**Moment bound (T5).** Fix `β≠α`. Slots `x∈A=[β]` (row `x`, offset `o(x)`), `Z_x=Q_xY_x`, `Y_x=Y^X_{x,(α,o(x))}`; weights `T_x=W^{-d}1_{[β]}` (`BoundedWeight`, `c=W^{-d}`, mass `1`: `uniformWeight_blockAvg2`). Interface `famGain(B,ρ,M,K)`: `∫∏_i‖applyOps(L_i)(qRow(x_i)(Y_{x_i}))‖≤B^{#ι}ρ^{Σnumq}` for words whose rows are distinct, `≠x_i` and **in `A`**. Conclusion `E|Σ_xT_xZ_x|^{2p}≤F_p(ρB)^{2p}` (T5), `M=K=2p`, `ρ=4δ`, `B=2(4C_Mδ+2δ)` (band form `minorDiffGainUpTo'_goodEvent`, G5b). Proof = the merged graded iteration (`:566`), with `hgain` asked only for `OpsOkOut` words (the invariant of `:610` has `∃j, x.2=k j`), conjugates by `epsHom`. **Pairings:** the slot index is the offset `o` alone (`y_x=(α,o)` is a function of `o`); rows `x↦u_o` are injective, so lone slots, the count `2#image≤#ι+#lone` and `Σ_vΠ|T_{v_i}|≤(n+1)n^n(Kρ)^n` (`sum_weighted_le`) are the one-block ones: the two-block structure creates no further index. **Gain per letter:** `ρ=4δ`; `Q_κ` on slot `i` has `κ=u_{o_j}`, `o_j≠o_i`, so `κ∉I={u,N(u),y}`: atoms `G_{uκ},G_{lκ},G_{κy}` are cross-offset (G.3). **Result:** `|W^{-d}Σ_oQ_{u_o}Y_o|≺ρB=O(δ_n²)` with `c=W^{-d}≤ρ²⇔δ≥W^{-d/2}/4`, true as `δ_n≥Ψ_n≥W^{-d/2}`.
**Numbers of moments and union.** `p=⌈(D+2/𝔠+1)/(2τ)⌉` (`N≤W^{1/𝔠}`, `≤N²` pairs `(β,α)`, `≤N` blocks `a`); `M=K=2p`. Uniform in `b'`: no constant depends on `(β,α)`; weights `|M^B_{ab'}|` summed by `ρ_row` (`BAMB_row_l1`).
**Remainders (m5, to G5b).** `|E_u[𝔛Δ_uu]|`, `|E_u[A_uΔ_uu]|≲δ²`: Cauchy-Schwarz with `E_u|𝔛|²=tW^{-d}Σ_v|G^{(u)}_{vy}|²` and the row-slice `P_u(Ω^c)≤ε` of `badStep`; Gaussian moments of `𝔛`, `1/G_uu` (polynomial in the row).

### G.6 (v) The averaged law it feeds (T6, T7); G5b
- **Exact identity** (`(P5)`, `1e-15`): `⟨M𝒦⟩_a:=W^{-d}Σ_oΣ_{b'}M^B_{ab'}𝒦_{(b',o)(a,o)}=Σ_{b'}M^B_{ab'}[t v̄_{b'}avg_oΔ_{(b',o)(a,o)}-M^B_{b'a}avg_o𝒜'_{(b',o)}-avg_o𝒜'_{(b',o)}Δ_{(b',o)(a,o)}-avg_o𝔛_{(b',o)(a,o)}]` (`𝔛_uu=0`); and `v̄_a-tΣ_bM^B_{ab}M^B_{ba}v̄_b=⟨M𝒦⟩_a` (`GreenCore_E3`, `GreenCore_coupled`).
- **Bounds on `Ω_δ`:** first and third terms `≤ρ_rowδ²·C`; second and fourth by (E)+T5: `|avg𝒜'|,|avg𝔛|≺δ_n²` uniformly in `b'`, summed with `ρ₂≤1` and `ρ_row`; then `BAStab` (`baStab_of_real`, `16κ⁻⁴`): `|v̄_a|≺Ψ²`. The entrywise law enters as the hypothesis `BAGiiGEX` (`‖Δ‖_max≺Ψ` from `(initialGT2)`: `max𝓛≺Ψ²`, `W^{-d}≤Ψ²`); the event `{‖Δ‖_max≤W^{τ}Ψ}` has probability `≥1-3W^{-D}` (`P(Ω^c)≤W^{-D}` from `(initialGT2)`, and `1_Ω‖Δ‖²≤W^{τ}max𝓛` with `max𝓛≤W^{τ}Ψ²` w.h.p.).
- **Order of quantifiers of the owed pin:** `∀κ ε 𝔡 (>0)`, `∀𝔠 sz z` with `BAFlow`, `∀t`, `0≤t≤BAflowT0`, `∀ε₀>0`, `BAGiiGEX sz z t ε₀`, `∀Ψ` (window `W^{-d/2}≤Ψ≤W^{-ε₀}`, `STInitialGT2gL`), then `PrecL` (`∀τ,D`). No `∃c` before the flow (unlike `BAGbEXPij'`): the constants `K_Y,ρ_row,K_Θ` depend on `(d,κ,𝔡)` only and only enter the `≺` constant. `BAGbEXPav` follows from `BAFAav`, `baStab_of_real` and `GreenCore_E3` (G6b; `L^{(1)}_{t,+,a}-m=v̄_a` to be matched there).
- **G5b's 1a need not be a design gate**: the FA moment bound is written here in its Lean form (G.8 S5, S6). G5b = twin of `Green/MinorDiffCond` for the two families (`badTower`, `hsmall` from `baLDEin_holds` and `P(Ω^c)≤W^{-D}`), the conditional-mean estimates (m5), `BAFamGain`, `BAFAav`: an ordinary preflight, with row 9 of the table in its exponent table.

### G.7 (vi) C1 and G2
Only uniform facts: `κ` uniform in `L` (`0.5/0.25/0.04`), `Λ=𝔡⁻¹=10`; `g` enters only through `g₀≤Λ` (`K_Y`, `K'_Y`: row 8) and `ρ_row` (row 10); every constant is `(d,κ,𝔡)` only; `g=1/64,1,10` checked in rows 1-11 and `(P1)-(P5)`. Not used: `g≤W^{-ε}`, smallness of `‖M-m₀I‖` (the argument centres at `M` and uses `M_{xκ}=0` only), `(Cλ)^{|a-b|}`, `c_λ`, `K_BA`.

### G.8 (vii) Pins (pseudo-Lean: statements only, no proofs, not compiled; for the compile step into `RBM3D/Probe/T2401Pins.lean`, never merged), files, split
Namespace `RBM.BA`, stem `GreenMinor_`, `V:=Vtx d L W`, `hM : ∀ u v, M u v = if u.2=v.2 then Mb u.1 v.1 else 0`, `hMd : ∀ a, Mb a a = m`.
```
def GreenMinor_T (β : Zd d L) (o : Fin (W^d)) : Set V := {x | x.2 = o ∨ x.1 = β}
def GreenMinor_R (β : Zd d L) (o : Fin (W^d)) : Set V := {x | x.1 = β ∧ x.2 ≠ o}
structure GreenMinor_Tower (G : Matrix V V ℂ) (Gs : Finset V → Matrix V V ℂ) : Prop where
  base : Gs ∅ = G
  step : ∀ S κ, κ ∉ S → ∀ x y, Gs (insert κ S) x y = greenMinor (Gs S) κ x y          -- (4.9)
-- S1  (T1)
theorem GreenMinor_removal (hκ : 0 < κ) (hw : κ/2 ≤ ‖G w w‖) (x y : V) :
    ‖greenMinor G w x y - G x y‖ ≤ (2/κ) * ‖G x w‖ * ‖G w y‖
theorem GreenMinor_cross (hM) (h : x.2 ≠ y.2) : M x y = 0
theorem GreenMinor_removal_cross (hM) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ) (hκ) (hw) (hxw : x.2 ≠ w.2) (hwy : w.2 ≠ y.2) :
    ‖greenMinor G w x y - G x y‖ ≤ (2/κ) * δ^2         -- one-sided versions: (2/κ) δ ‖G w y‖ (hxw), (2/κ) δ ‖G x w‖ (hwy)
-- S2  (T2)
def GreenMinor_good (Gs) (M) (κ δ : ℝ) (m₀ : ℕ) (β) (o) : Prop :=
  ∀ S : Finset V, ↑S ⊆ GreenMinor_R β o → S.card ≤ m₀ → ∀ x y, x ∈ GreenMinor_T β o → y ∈ GreenMinor_T β o → x ∉ S → y ∉ S →
    ‖Gs S x y - M x y‖ ≤ 2*δ ∧ κ/2 ≤ ‖Gs S x x‖
theorem GreenMinor_good_of_event (hM) (hMd) (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (hδ0 : 0 ≤ δ) (hδ4 : 4*δ ≤ κ) (hMδ : 8*m₀*δ ≤ κ)
    (hT : GreenMinor_Tower G Gs) (hG : ∀ x y, ‖G x y - M x y‖ ≤ δ) (β o) : GreenMinor_good Gs M κ δ m₀ β o
-- S3  (T3)
def GreenMinor_YA (G M D : Matrix V V ℂ) (s m : ℂ) (u : V) : ℂ := (s*(G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m
def GreenMinor_YX (G M D) (s m) (u y : V) : ℂ := M u y * (s*(G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m
    + (∑ l, D u l * (G l y - M l y) - s*(G u y - M u y))
    + ((G u u - M u u) * ∑ l, D u l * (G l y - M l y) - (G u y - M u y) * ∑ l, D u l * (G l u - M l u)) / m
theorem GreenMinor_Arow_eq (hGR hRG hMR hz hM hMd (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀:ℂ) else 0) (hG0 : G u u ≠ 0)) :
    GreenCore_Arow G X D t m u = GreenMinor_YA G M D s m u * m / G u u
theorem GreenMinor_Xrow_eq (… same …) (hyu : y ≠ u) : GreenCore_Xrow G X u y = -(GreenMinor_YX G M D s m u y * m / G u u)
theorem GreenMinor_split_A : GreenCore_Arow … = YA - GreenCore_Arow … * (G u u - m) / m      -- and `_split_X`: 𝔛 = -YX - 𝔛 (G u u - m)/m
theorem GreenMinor_YA_le / GreenMinor_YX_le (hL : 3 ≤ L) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ') (hκ : κ ≤ ‖m‖) (hMuy : ‖M u y‖ ≤ 1) :
    ‖YA …‖ ≤ (‖s‖ + 2*d*g₀)/κ * δ'   ∧   ‖YX …‖ ≤ ((‖s‖ + 2*d*g₀)*(1/κ + 1) + 4*d*g₀*δ'/κ) * δ'
-- S4  (T4)
def GreenMinor_a (κ : ℝ) : ℕ → ℝ | 0 => 2/κ | r+1 => 16^r * GreenMinor_a κ r ^ 5
def GreenMinor_cY (d : ℕ) (κ g₀ s : ℝ) (r : ℕ) : ℝ := (s + 2*d*g₀)*(1/κ + 1) * GreenMinor_a κ r + (4*d*g₀/κ) * 2^r * GreenMinor_a κ r ^ 2
theorem GreenMinor_diff (hT) (hgood : GreenMinor_good Gs M κ δ m₀ β o) (hu : u = (β,o)) (hy : y.2 = o ∧ y.1 ≠ β) (l : List V) (hl : l.Nodup)
    (hR : ∀ k ∈ l, k ∈ GreenMinor_R β o) (hlen : l.length ≤ m₀) (h2δ : 2*δ ≤ 1) :
    ‖iterDeltaFam l (fun S => GreenMinor_YX (Gs S) M D s m u y) ∅‖ ≤ GreenMinor_cY d κ g₀ ‖s‖ l.length * (2*δ)^(l.length+1)
    ∧ (same bound with GreenMinor_YA (Gs S) M D s m u)
-- S5  (T5)
def GreenMinor_famGain (sz : Sizes d) (n : ℕ) (A : Finset (Idx d (sz.L n) (sz.W n))) (Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ) (B ρ : ℝ) (M K : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧ ∀ (ι : Type) [Fintype ι] (k : ι → Idx d (sz.L n) (sz.W n)) (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))),
    (∀ i, k i ∈ A) → (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i ∧ x.2 ∈ A) → (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ K →
    ∫ ω, ∏ i, ‖applyOps sz n (L i) (qRow sz n (k i) (Y (k i))) ω‖ ∂(Sizes.seqP sz) ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)
theorem GreenMinor_famAvg_moment (hY : ∀ k, BddMeas sz (Y k)) (hYd : ∀ k, FinDep sz (Y k)) (hg : GreenMinor_famGain sz n A Y B ρ M K)
    (hM : 2*p ≤ M) (hK : 2*p ≤ K) (hρ1 : ρ ≤ 1) (hcρ : c ≤ ρ^2) (hw : BoundedWeight T c A) (hp : 2*p ≤ A.card) :
    ∫ ω, ‖∑ k ∈ A, (T k : ℂ) * qRow sz n k (Y k) ω‖ ^ (2*p) ∂(Sizes.seqP sz) ≤ (2*p+1) * (2*p)^(2*p) * (2^(2*p-1) * ρ * B)^(2*p)
-- S6  (T6) exact averaging identity: statement above (G.6), hypotheses of GreenCore_E3
-- S7  (T7, owed pins; registry lines `RBM.BA.BAFamGain` (famGain at the carrier for Y^A, Y^X, eventually in n; owner BA-G5b) and `RBM.BA.BAFAav` (owner BA-G5b; consumer BA-G6b))
def BAFAav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
   ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t ε₀ →
   ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) → (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
   STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
     PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
       (fun n a ω => ‖(((sz.W n : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, ∑ b', BAMB … a b' * GreenCore_K (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n (t n) ω) (GreenCore_Dc sz z n) (t n) m (b', o) (a, o)‖)
       (fun n _ _ => Ψ n ^ 2)
```
Nonempty instances (1b; `d=3`, `t=1/2`, data as T2390 (a′) D4): S1-S4 at the explicit in-block `X≠0`, `G=(H-z)⁻¹`, `δ=1/64·κ`; S5 at `W=2` (`c=1/8≤ρ²=1/4`), `famGain` a hypothesis; S2 also at `Δ:=δ·E` of D4.
| file | rows (basis) | lo / central / hi |
|---|---|---|
| `BA/GreenMinor.lean` (G5a1) | V+S1 (new) 130/170/250; R1 minor expansion over `D+X` (`greenSetMat` twin, `FinDepOffRows` by `RowIndep_submatrix_shift_congr`, `applyOps_eq_applyOps_minorDiff` twin; band G 749 × TW `0.73/0.97/1.61`) 547/727/1206; R2 protected good event (band T 192 × NW `0.85/1.37/2.10`) 163/263/403; H+I 100/140/220 | `940 / 1300 / 2079` |
| `BA/GreenMinor2.lean` (G5a2) | R3 families, entry forms, splits, base bounds (new) 250/380/560; R4 grading twin + sum rule (T 430 × NW + 40) 406/629/943; R6 graded iteration + moment twin (`FlucIterGain:566-895`, about 330 × TW) 241/320/531; R7 S6 + pins + registry 120/160/240; H+I 100/150/230 | `1117 / 1639 / 2504` |
`TW, NW` as T2378 §5. Total `2057 / 2939 / 4583` against T2378's `1123/1642/2617` for this row (the families, the sum rule and the family moment twin R6 were not counted there). Over 1500: split as shown. **Cut rule:** R6 (own section, imports only merged files and R3's vocabulary) moves to `BA/GreenMinor3.lean` if `GreenMinor2` passes 1700 lines; no cut inside a closure. Route B (+350 lines, optional primed successor `GreenMinor_cY'`) only if the `hB1` thresholds must be moderate.

### G.9 Findings, risks, paper-delta candidates
- **F1** The merged moment bound `integral_norm_flucAvg_pow_le_iter_budget` is specific to `flucDiag` and its `hgain` covers all `OpsOk` words (rows anywhere): at BA a row outside the block of the slot has no gain (control `(P3)`, `25-27`): the family twin (R6) is new work, not in T2378 §5.
- **F2** `BddMeas` forces the polynomial surrogates (G.4); `DiffBd` has no sum rule; Route A constants give `hB1` thresholds `10^{33-91}` (eventual only), Route B `10^{3-7}`.
- **R-a** (G5b) the conditional means (m5) involve unbounded Gaussian forms and `1/G_uu`; **R-b** `DiffBd` on protected levels (`S⊆R`) needs a guard or the subtype `↥R`; **R-c** `M=2p` grows with the moment order: `c_m` is fixed before `n`, the thresholds are eventual.
- **T2401a** the averaged law, second half of `(GiiGEX_BA)` (`7_8:1931-1933`; the label `GavLGEX_BA` is commented out, `:1936`), is proved for all `g≤Λ`: the cited route needs `g≤W^{-ε}` (T2378 F2); the argument is (E3) plus FA of the two families, statement unchanged. **T2401b** the family gain interface restricts word rows to the block: `FlucGainUpTo'` is not a special case. **T2401c** `a_0=2/κ` replaces the band's `2` in `atomC`.

## (a″) Probe compile — Sun Oct 11 03:28:18 UTC 2026
Step role `prover-max` (claude-sonnet-5-5); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2401`, branch `t/T2401`, commit `a48c0ce`: one file, `RBM3D/Probe/T2401Pins.lean` (767 lines, never merged, no root import). Sections (a) and (G) are not edited. Scripts: `docs/reports/T2401/probe_chk.py`, `probe_chk.out`. No port from RBM1D/RBM2D.
Compile at `date -u` = Sun Oct 11 03:26:03 UTC 2026 (committed state; command, verbatim output, exit code):
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2401 && lake env lean RBM3D/Probe/T2401Pins.lean
RBM.BA.GreenMinor_T {d L W : ℕ} (β : Zd d L) (o : Fin (W ^ d)) : Set (Vtx d L W)
RBM.BA.GreenMinor_R {d L W : ℕ} (β : Zd d L) (o : Fin (W ^ d)) : Set (Vtx d L W)
RBM.BA.GreenMinor_Tower {d L W : ℕ} (G : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ) : Prop
RBM.BA.GreenMinor_good {d L W : ℕ} (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ)
  (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (κ δ : ℝ) (m₀ : ℕ) (β : Zd d L) (o : Fin (W ^ d)) : Prop
RBM.BA.GreenMinor_YA {d L W : ℕ} [NeZero L] (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u : Vtx d L W) : ℂ
RBM.BA.GreenMinor_YX {d L W : ℕ} [NeZero L] (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u y : Vtx d L W) : ℂ
RBM.BA.GreenMinor_a (κ : ℝ) : ℕ → ℝ
RBM.BA.GreenMinor_cY (d : ℕ) (κ g₀ s : ℝ) (r : ℕ) : ℝ
RBM.BA.GreenMinor_famGain {d : ℕ} (sz : Sizes d) (n : ℕ) (A : Finset (Idx d (sz.L n) (sz.W n)))
  (Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ) (B ρ : ℝ) (M K : ℕ) : Prop
RBM.BA.GreenMinor_avg {d W : ℕ} (f : Fin (W ^ d) → ℂ) : ℂ
RBM.BA.GreenMinor_avgK {d L W : ℕ} [NeZero L] [NeZero W] (G M X D : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  (Mb : Zd d L → Zd d L → ℂ) (t : ℝ) (m : ℂ) (a : Zd d L) : ℂ
RBM.BA.GreenMinor_removal_pin : Prop
RBM.BA.GreenMinor_cross_pin : Prop
RBM.BA.GreenMinor_removal_crossL_pin : Prop
RBM.BA.GreenMinor_removal_crossR_pin : Prop
RBM.BA.GreenMinor_removal_cross_pin : Prop
RBM.BA.GreenMinor_offset_ne_pin : Prop
RBM.BA.GreenMinor_good_of_event_pin : Prop
RBM.BA.GreenMinor_Arow_eq_pin : Prop
RBM.BA.GreenMinor_Xrow_eq_pin : Prop
RBM.BA.GreenMinor_split_A_pin : Prop
RBM.BA.GreenMinor_split_X_pin : Prop
RBM.BA.GreenMinor_YA_le_pin : Prop
RBM.BA.GreenMinor_YX_le_pin : Prop
RBM.BA.GreenMinor_diff_pin : Prop
RBM.BA.GreenMinor_diff_pin' : Prop
RBM.BA.GreenMinor_famAvg_moment_pin : Prop
RBM.BA.GreenMinor_avgK_pin : Prop
RBM.BA.GreenMinor_avg_split_pin : Prop
RBM.BA.BAFAav (d : ℕ) : Prop
EXIT=0
```
Scope and hygiene (script output):
```
$ lake build --no-build RBM3D.BA.GreenCore RBM3D.Green.FlucIterGain RBM3D.Green.MinorDiff | tail -1
All targets up-to-date (3781 jobs).
$ grep -nE 'sorry|admit|axiom|native_decide' RBM3D/Probe/T2401Pins.lean; echo grep-exit=$?
grep-exit=1
$ git --no-optional-locks diff --stat main...t/T2401
 RBM3D/Probe/T2401Pins.lean | 767 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 767 insertions(+)
$ git rev-parse --short main
3e72137
$ git grep -n -e GreenMinor -e BAFAav -e BAFamGain main -- RBM3D RBM3D.lean | wc -l
       0
$ git rev-parse --short HEAD; wc -l RBM3D/Probe/T2401Pins.lean
a48c0ce
     767 RBM3D/Probe/T2401Pins.lean
```
**Pins and instances** (probe line numbers; every `example` applies the pin as a hypothesis, the deterministic hypotheses are discharged by `norm_num`/`simp`/`decide` or by public lemmas: `GreenCore_carrier`, `BAflow_real`, `uniformWeight_blockAvg2`, `flucVanish_card_blockSupport`):
| G.8 | pins | example, data |
|---|---|---|
| vocabulary | `T` 46, `R` 49, `Tower` 52, `good` 59, `YA` 65, `YX` 69 | |
| S1, (ii) | `removal` 79, `cross` 85, `crossL` 90, `crossR` 96, `removal_cross` 102, `offset_ne` 109 | 373, 384, 388, 409: hand-made datum |
| S2 | `good_of_event` 116 | 416: explicit tower, `δ = 1/100`, `κ = 1/2`, `m₀ = 3` |
| S3 | `Arow_eq` 128, `Xrow_eq` 140, `split_A` 152, `split_X` 164, `YA_le` 179, `YX_le` 186 | 558: carrier (`d = 3`, `sz0`, `n = 0`, `t = 1/2`, any `ω`); 520: hand-made |
| S4 | `a` 196, `cY` 201, `diff` 209, `diff'` 224 | 416 (`diff'`, `l = [q]`); 690: `¬ GreenMinor_diff_pin` |
| S5 | `famGain` 241, `famAvg_moment` 252 | 637: `sz0`, `n = 0`, `A = [β]`, `p = 1`, `ρ = 1/100` (the instance of (a)(ii) has `W = 2`; `sz0` has `W = 32`) |
| S6 | `avg` 263, `avgK` 266, `avgK_pin` 271, `avg_split` 283 | 587: carrier |
| S7 | `BAFAav` 297 | 663: `flow_sz0`, `t ≡ 1/2`, `ε₀ = 1/10`, `Ψ = W^{-1}` |
Hand-made datum (:345-:367): `d = 3`, `L = 3`, `W = 2`, `m = i`, `M = m·1`, `Δ = ε(E_pq + E_qp)`, `p = (0,0)`, `q = (0,1)` (one block, offsets `0 ≠ 1`), `ε = δ = 1/100`, `g₀ = 1/10`; its tower (:416) is explicit (`G^{(q)}_{pp} = m - ε²/m`). Hypotheses left in the examples: the pin, `GreenMinor_famGain` (G5b), `BAGiiGEX` (G6), `STInitialGT2gL` (the premise).
**Differences from the displayed pseudo-Lean of G.8** (each visible in the file):
- Theorem rows are closed `Prop`s `*_pin` (the probe has no proofs). S1 one-sided versions are two pins (G.8: a comment); S6 is two pins (G.6 identity, its split); `offset_ne` (:109) is added: the `T`/`R` offset fact of the recursion of S2 (ticket (ii)).
- Hypotheses made explicit (not shown in G.8): `0 ≤ g₀`, `hD`, `0 < κ` in `YA_le`, `YX_le`; `hL`, `0 ≤ g₀`, `hD`, `hM`, `0 < κ`, `κ ≤ ‖m‖`, `‖M u y‖ ≤ 1` in `diff` (without `hD`, `g₀` is not tied to `D`).
- Added: `m ≠ 0` in the four S3 identity pins (F2); `diff'` = `diff` with `κ ≤ 1` (F1, proposed repair, not G.8). Not written: `BAFamGain` (F3).
**Findings** (each backed by a compile or a script):
- **F1 (S4 as displayed is false).** `example : ¬ GreenMinor_diff_pin` (:690, compiled above): `κ = ‖m‖ = m = 4`, `g₀ = 0`, `s = 1`, `δ = 1/100`, `m₀ = 3`, `l = []`, `G = 4·1 + (1/50) E_{u,y}` (`u = (0,0)`, `y = (e_0,0)`), tower `Gs S = G` off `S`: the event holds on every protected level, `‖Y^X_{uy}‖ = 1/50 > c_Y(0)(2δ) = 1/80` (`probe_chk.out` F1). The base case needs `a_0 = 2/κ ≥ 1` (sketch: `YX_le` at `δ' = 2δ`); BA has `κ ≤ ‖m‖ ≤ 1` (`BAm_norm_le_one`, `BA/Ward.lean:136`). Proposed: S4 with `κ ≤ 1` (`diff'`, applied at :416); the dispatcher decides; 1b must not take the displayed S4.
- **F2 (S3 identities need `m ≠ 0`).** `A_u G_{uu} = sΔ_{uu} - Σ_l D_{ul} Δ_{lu}` holds for every `m`, and the right side of `Arow_eq` is `Y^A m / G_{uu}` with Lean `x/0 = 0`. A 3-site datum (`d = 1`, `L = 3`, `W = 1`, `g₀ = 1`, `s = 1`, `X = I/2`) satisfies every other hypothesis with `m = 0`, `A_u = 1/2`, right side `0` (`probe_chk.out` F2; numeric, not a Lean instance). In BA `m ≠ 0` (`κ ≤ ‖m‖`).
- **F3 (`BAFamGain`).** G.8 S7 names it ("famGain at the carrier for `Y^A`, `Y^X`, eventually in `n`") without Lean text; the carrier family on `Idx` and the constants `B`, `ρ` (G.5: `ρ = 4δ`, `B = 2(4C_Mδ + 2δ)`) are not fixed there, so it is not written. The registry line of 1b needs its `Prop`: the 1a-audit should fix it before 1b.
- **F4 (tower).** `GreenMinor_Tower.step` holds for all entries, removed rows included: `Gs (insert κ S) κ y = Gs S κ y - Gs S κ κ Gs S κ y / Gs S κ κ`, which is `0` only if `Gs S κ κ ≠ 0` (zero padding, as `gEnt`). It holds for the principal-submatrix resolvents of a Hermitian `H`, `Im z ≠ 0` (`green_diag_ne_zero`, `Green/LDE.lean:809`; `greenSetMat_insert_apply`, `Green/MinorGoodLe.lean:572`), so R1 must supply it. The 1b instance plan "S2 at `Δ := δE`" (G.8) has no closed-form tower; the probe datum has one (:416).
Numeric check of the Lean texts of S3, S6 (formulas copied from the file; `d = 2`, `L = 3`, `W = 2`) and of F1, F2:
```
$ cd docs/reports/T2401 && python3 probe_chk.py
(S3) max|Arow - YA m/G_uu| = 1.1e-15; max|Xrow + YX m/G_uu| = 9.6e-16; split_A 1.1e-15; split_X 9.2e-16
(S6) max|vbar_a - t sum Mb Mb vbar - avgK| = 2.2e-16; max|avgK - split| = 1.1e-16
(F1) kappa = 4.0: c_Y(0) (2 delta) = 0.01250; |Y^X| = |s| |Delta_uy| = 0.02000; violated: True
(F2) 3-site datum: m = -0.0e+00, G_uu = -0.2222; A_u = 0.5000; Lean value of YA*m/G_uu (x/0 = 0) = 0.0000; N_u = -0.1111
```
Paper-delta candidate: `T2401d` the Lean S4 carries `κ ≤ 1` (paper: `|m| ≤ 1` implicit in the BA data). Verdict of the probe step: compiles, `EXIT=0`; open for the 1a-audit: F1, F3 (and F2, F4 as observations).

## (a′) Preflight corrections — Sun Oct 11 04:25:32 UTC 2026
Rule (B) repair under Amend 1 (H201; `docs/tickets/T2401-amend-1.md`; answers `T2401-1a-audit.md` D1-D4). Mathematics and pseudo-Lean only; the probe step recompiles. Sections (a), (G), (a″) are not edited; where they disagree with this section, (a′) governs: G.6 lines 129-130, G.8 S4, S5, S7 and the file table. Script `docs/reports/T2401/replan_a2.py`, output `replan_a2.out`.

**D1 (T7 / (v)): hypothesis at `ε₀/2`, event inclusion.** `Ω(ε) = {‖G-M‖_max ≤ W^{-ε}}` is `indMax` of `BAGiiGEX` (`BA/Step1Boot.lean:79`). `Admissible 𝔠 𝔡` gives `N^𝔠 ≤ W` eventually (`Defs/Sizes.lean:168`, `N = (WL)^d`). Put `ζ = 𝔠ε₀/2`. Then `N^ζ W^{-ε₀} ≤ W^{-ε₀/2}`, so `{‖Δ‖_max ≤ N^ζ W^{-ε₀}} ⊆ Ω(ε₀/2)` (this is the amend's `Ω(ε₀/2) ⊇ {‖Δ‖_max ≤ W^{τ-ε₀}}`, `τ = ζ/𝔠 ≤ ε₀/2`). The first conjunct of `(initialGT2)` (`STInitialGT2gL`, `Chain/Carrier.lean:140`) at `τ = ζ` gives `P(Ω(ε₀/2)^c) ≤ N^{-D}` for every `D`. `BAGiiGEX(ε₀/2)` gives `1_{Ω(ε₀/2)} |Δ_{xy}|² ≺ max 𝓛`, and the second conjunct gives `max 𝓛 ≺ Ψ²`. Hence `P(‖Δ‖_max > N^τΨ) ≤ P(Ω(ε₀/2)^c) + P(∃x,y: 1_Ω|Δ_xy|² > N^{2τ}Ψ²) ≤ N^{-D}`, i.e. `‖Δ‖_max ≺ Ψ`; the union over `(x,y)` is inside `PrecL`. This replaces the sentence "`P(Ω^c) ≤ W^{-D}` from (initialGT2)" of G.6. The window `Ψ ≤ W^{-ε₀}` is used only for `δ_n = W^τΨ_n ≤ W^{τ-ε₀}` (smallness of T2, T4).
Corrected pin (the only change is the hypothesis; `G6`'s `BAGbEXPii` gives it for every `ε₀`):
```
def BAFAav (d : ℕ) : Prop :=  -- G.8 S7 with   BAGiiGEX sz z t ε₀   replaced by   BAGiiGEX sz z t (ε₀/2)
  ∀ κ ε 𝔡, 0<κ → 0<ε → 0<𝔡 → ∀ 𝔠 sz z, BAFlow sz κ ε 𝔠 𝔡 z → ∀ t, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
   ∀ ε₀, 0<ε₀ → BAGiiGEX sz z t (ε₀/2) → ∀ Ψ, (W^{-d/2} ≤ Ψ n ev.) → (Ψ n ≤ W^{-ε₀} ev.) →
   STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ → PrecL … (same conclusion as G.8 S7)
```
Probe instance (:663): `hii : BAGiiGEX sz0 zSeq (fun _ => 1/2) (1/20)` (`ε₀ = 1/10` unchanged; `ε₀/2 = 1/20`). Numbers below: `N^ζW^{-ε₀}` against `W^{-ε₀/2}`.

**D2 (S4).** S4 of G.8 is `GreenMinor_diff_pin'` (probe :224: the pin of G.8 with the extra hypothesis `κ ≤ 1`; BA supplies `κ ≤ ‖m‖ ≤ 1`, `BA/Ward.lean:136`). `GreenMinor_diff_pin` stays only as the record (`¬ GreenMinor_diff_pin`, probe :690). Base case: `a_0 = 2/κ ≥ 1` gives `(‖s‖+2dg₀)(1/κ+1) ≤ (‖s‖+2dg₀)(1/κ+1)a_0` and `4dg₀δ'/κ ≤ (4dg₀/κ)a_0²` for `δ' = 2δ ≤ 1`; `a_{r+1} = 16^r a_r^5 ≥ a_r` from `a_r ≥ 1`. Paper-delta `T2401d` stays. 1b must take `diff'`.

**D3 (S7): `BAFamGain`** (registry owed line, owner BA-G5b; consumer `BAFAav`'s proof). Data of G.5: `ρ = 4δ_n`, `B = Cδ_n` (`≥ 2(4C_Mδ_n+2δ_n)`, `C` fixed by `(d,κ,𝔡,p)` before `n`), `M = K = 2p`, `A = [β]`, `δ_n = W^τΨ_n`; events and window as in D1:
```
def BAFamGain (d : ℕ) : Prop :=
  ∀ κ ε 𝔡, 0<κ → 0<ε → 0<𝔡 → ∀ 𝔠 sz z, BAFlow sz κ ε 𝔠 𝔡 z → ∀ t, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
   ∀ ε₀, 0<ε₀ → BAGiiGEX sz z t (ε₀/2) → ∀ Ψ, (W^{-d/2} ≤ Ψ n ev.) → (Ψ n ≤ W^{-ε₀} ev.) →
   STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ → ∀ τ, 0<τ → τ ≤ ε₀/2 → ∀ p : ℕ,
   ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ β α : Zd d (sz.L n), β ≠ α →
     let δ := (W n : ℝ)^τ * Ψ n;  let A := univ.filter (·.1 = β);  let G,M,D,s,m := GreenCore_Gc/Mc/Dc sz z n (t n) ω, (E+m), BAmF
     famGain (sz.withLam 0) n A (fun x ω => GreenMinor_YA G M D s m x) (C*δ) (4*δ) (2*p) (2*p) ∧
     famGain (sz.withLam 0) n A (fun x ω => GreenMinor_YX G M D s m x (α, x.2)) (C*δ) (4*δ) (2*p) (2*p)
```
(`famGain` is `GreenMinor_famGain` of probe :241, now G5b's vocabulary; `ρ ≤ 1` and `c = W^{-d} ≤ ρ² = 16δ²` follow from `δ_n ≥ Ψ_n ≥ W^{-d/2}` and `δ_n ≤ W^{-ε₀/2}`.) Nonempty instance for the probe: `example (h : BAFamGain 3) (hii : BAGiiGEX sz0 zSeq (fun _ => 1/2) (1/20)) …` at `flow_sz0`, `t ≡ 1/2`, `ε₀ = 1/10`, `Ψ = W^{-1}`, `τ = 1/20`, `p = 1`, conclusion `:= h … ` (the `famGain` content is the hypothesis `h`), as the `BAFAav` instance (:663).

**D4 (file plan).** R6 (`FlucIterGain:566-895` twin: S5 `famGain`, `famAvg_moment`) moves to G5b with `BAFamGain`, `BAFAav` and the outputs of G.6. R1 stays: it supplies `GreenMinor_Tower` for the real principal-submatrix resolvents (F4 of (a″)). Rows are the (G.8) rows, R6 removed, `H+I` of the second file (100/150/230) split in half. With R6 gone the total hi is 4052 > 2·2000, so no split into two files meets the 2,000 stop line, and Amend 1 authorises the third file (split by section, never inside a proof; imports in the order below):
| file | rows | lo / central / hi |
|---|---|---|
| `BA/GreenMinor.lean` | V+S1 130/170/250; R1 547/727/1206; H+I 100/140/220 | 777 / 1037 / 1676 |
| `BA/GreenMinor2.lean` (imports `GreenMinor`) | R2 163/263/403; R3 250/380/560; H+I 50/75/115 | 463 / 718 / 1078 |
| `BA/GreenMinor3.lean` (imports `GreenMinor2`) | R4 406/629/943; R7 (S6, registry incl. `BAFamGain`, `BAFAav`) 120/160/240; H+I 50/75/115 | 576 / 864 / 1298 |
Total `1816 / 2619 / 4052` against the ticket's `1100 / 1650 / 2600`: central ratio 1.59 (cause: the families R3, the sum rule in R4, the vocabulary, not counted in T2378 §5). Every file is under 1,500 central and 2,000 hi; the stop line stays 2,000 per file. 1b targets: S1 (with `removal_cross`, `offset_ne`), S2, S3, S4 as `diff'`, S6, the tower for real minors (R1), registry owed lines `BAFamGain`, `BAFAav`. S5 is G5b's.
```
$ cd docs/reports/T2401 && python3 replan_a2.py
(D1) N=(W L)^d, c=Bandwidth exponent, zeta=c*eps0/2: N^zeta*W^-eps0 vs W^(-eps0/2), and N^c<=W
  W=2^24,L=64 eps0=1.0: log2 N=90.0; N^c<=W: True (log2 N^c=15.00, log2 W=24); zeta=0.08333; log2 lhs=-16.500 <= log2 rhs=-12.000: True (slack 2^4.500)
  W=2^24,L=64 eps0=1.5: log2 N=90.0; N^c<=W: True (log2 N^c=15.00, log2 W=24); zeta=0.12500; log2 lhs=-24.750 <= log2 rhs=-18.000: True (slack 2^6.750)
  sz0 W=32,L=4 eps0=0.1: log2 N=21.0; N^c<=W: True (log2 N^c=3.50, log2 W=5); zeta=0.00833; log2 lhs=-0.325 <= log2 rhs=-0.250: True (slack 2^0.075)
(D2) kappa<=1: base coefficient (|s|+2dg0)(1/k+1)+4dg0*delta'/k at delta'=1 (2*delta<=1) vs c_Y(0)=(|s|+2dg0)(1/k+1)a0+(4dg0/k)a0^2, a0=2/k; and a_r monotone
  g=0.015625 kappa=0.5: a0=4; base=3.545 <= c_Y(0)=17.92: True; a_r monotone r<=3: True
  g=1 kappa=0.25: a0=8; base=44.94 <= c_Y(0)=1798: True; a_r monotone r<=3: True
  g=10 kappa=0.04: a0=50; base=961 <= c_Y(0)=1.588e+06: True; a_r monotone r<=3: True
  g=None kappa=4.0: a0=0.5; base=1.25 <= c_Y(0)=0.625: False; a_r monotone r<=3: False
(D4) rows lo/central/hi from (G.8); R6 (241/320/531) removed; H+I of file 2 (100/150/230) split with R6 gone as stated
  total (R6 removed): [1816, 2619, 4052]  [with R6:  [2057, 2939, 4583] ]
  two files possible under hi<=2000 per file? total hi 4052 <= 4000: False
  GreenMinor  (V+S1, R1, H+I): lo/central/hi = 777/1037/1676; hi<=2000: True; central<=1500: True
  GreenMinor2 (R2, R3, H+I): lo/central/hi = 463/718/1078; hi<=2000: True; central<=1500: True
  GreenMinor3 (R4, R7, H+I): lo/central/hi = 576/864/1298; hi<=2000: True; central<=1500: True
  sum of the three: [1816, 2619, 4052] ticket frame 1100/1650/2600; central ratio 1.59
```
(Row `kappa=4.0` is the record of the false displayed pin: `a_0 = 1/2 < 1`, base coefficient `1.25 > c_Y(0) = 0.625`.)

**Verdicts after (a′).** T1 PASS, T2 PASS, T3 PASS, T4 PASS (`κ ≤ 1`, D2), T5 PASS (statement unchanged; now G5b's, D4), T6 PASS, T7 PASS (`BAGiiGEX(ε₀/2)`, D1; `BAFamGain` stated, D3). (iv) still closes: no REQ.

## (a‴) Probe recompile (Amend 1) — Sun Oct 11 04:36:56 UTC 2026
Step role `prover-max` (claude-sonnet-5-5), after (a′). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2401`, branch `t/T2401`, commit `aec5a16` (parent `a48c0ce` of (a″)): one file, `RBM3D/Probe/T2401Pins.lean` (847 lines, never merged, no root import). Sections (a), (G), (a″), (a′) are not edited. Amend 1 D1-D3 are applied as (a′) states them; D4 (file plan) has no probe content (one comment in section 5 of the file). No port from RBM1D/RBM2D. The file has definitions, `*_pin : Prop` rows, 33 `#check` lines and 14 `example`s (30 and 11 in `a48c0ce`); no theorem, no `sorry`.
Compile at `date -u` = Sun Oct 11 04:33:59 UTC 2026 (committed state `aec5a16`; command, verbatim output, exit code):
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2401 && lake env lean RBM3D/Probe/T2401Pins.lean; echo EXIT=$?
RBM.BA.GreenMinor_T {d L W : ℕ} (β : Zd d L) (o : Fin (W ^ d)) : Set (Vtx d L W)
RBM.BA.GreenMinor_R {d L W : ℕ} (β : Zd d L) (o : Fin (W ^ d)) : Set (Vtx d L W)
RBM.BA.GreenMinor_Tower {d L W : ℕ} (G : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ) : Prop
RBM.BA.GreenMinor_good {d L W : ℕ} (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ)
  (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (κ δ : ℝ) (m₀ : ℕ) (β : Zd d L) (o : Fin (W ^ d)) : Prop
RBM.BA.GreenMinor_YA {d L W : ℕ} [NeZero L] (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u : Vtx d L W) : ℂ
RBM.BA.GreenMinor_YX {d L W : ℕ} [NeZero L] (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u y : Vtx d L W) : ℂ
RBM.BA.GreenMinor_a (κ : ℝ) : ℕ → ℝ
RBM.BA.GreenMinor_cY (d : ℕ) (κ g₀ s : ℝ) (r : ℕ) : ℝ
RBM.BA.GreenMinor_famGain {d : ℕ} (sz : Sizes d) (n : ℕ) (A : Finset (Idx d (sz.L n) (sz.W n)))
  (Y : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ) (B ρ : ℝ) (M K : ℕ) : Prop
RBM.BA.GreenMinor_avg {d W : ℕ} (f : Fin (W ^ d) → ℂ) : ℂ
RBM.BA.GreenMinor_avgK {d L W : ℕ} [NeZero L] [NeZero W] (G M X D : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  (Mb : Zd d L → Zd d L → ℂ) (t : ℝ) (m : ℂ) (a : Zd d L) : ℂ
RBM.BA.GreenMinor_famA {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (n : ℕ) : Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ
RBM.BA.GreenMinor_famX {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (n : ℕ) (α : Zd d (sz.L n)) :
  Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ
RBM.BA.GreenMinor_removal_pin : Prop
RBM.BA.GreenMinor_cross_pin : Prop
RBM.BA.GreenMinor_removal_crossL_pin : Prop
RBM.BA.GreenMinor_removal_crossR_pin : Prop
RBM.BA.GreenMinor_removal_cross_pin : Prop
RBM.BA.GreenMinor_offset_ne_pin : Prop
RBM.BA.GreenMinor_good_of_event_pin : Prop
RBM.BA.GreenMinor_Arow_eq_pin : Prop
RBM.BA.GreenMinor_Xrow_eq_pin : Prop
RBM.BA.GreenMinor_split_A_pin : Prop
RBM.BA.GreenMinor_split_X_pin : Prop
RBM.BA.GreenMinor_YA_le_pin : Prop
RBM.BA.GreenMinor_YX_le_pin : Prop
RBM.BA.GreenMinor_diff_pin : Prop
RBM.BA.GreenMinor_diff_pin' : Prop
RBM.BA.GreenMinor_famAvg_moment_pin : Prop
RBM.BA.GreenMinor_avgK_pin : Prop
RBM.BA.GreenMinor_avg_split_pin : Prop
RBM.BA.BAFamGain (d : ℕ) : Prop
RBM.BA.BAFAav (d : ℕ) : Prop
EXIT=0
```
Scope and hygiene (script output):
```
$ grep -nE 'sorry|admit|axiom|native_decide' RBM3D/Probe/T2401Pins.lean; echo grep-exit=$?
grep-exit=1
$ git --no-optional-locks diff --stat main...t/T2401
 RBM3D/Probe/T2401Pins.lean | 847 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 847 insertions(+)
$ git --no-optional-locks grep -n -e GreenMinor -e BAFAav -e BAFamGain main -- RBM3D RBM3D.lean | wc -l
       0
$ git rev-parse --short HEAD; wc -l RBM3D/Probe/T2401Pins.lean
aec5a16
     847 RBM3D/Probe/T2401Pins.lean
```
**Changes against (a″)** (probe line numbers of `aec5a16`; the new and changed `example`s apply the pin as a hypothesis; deterministic hypotheses are discharged by `norm_num`, `flow_sz0`, `half_lt_t0`, `Real.rpow_le_rpow_of_exponent_le` (D1, D3) and `BAflow_real`, `BAm_norm_le_one` (D2)):
| Amend 1 | statement in the probe | nonempty instance |
|---|---|---|
| D1 | `BAFAav` :337 takes `BAGiiGEX sz z t (ε₀ / 2)` (:339); nothing else of its statement changed | :721 `sz0`, `flow_sz0`, `t ≡ 1/2`, `ε₀ = 1/10`, `Ψ = W^{-1}`; `hii` at `ε₀/2 = 1/20` (one `rw` to the literal `1/10/2`); :716 `BAGbEXPii 3` (`BA/Step1Boot.lean:108`, `∀ ε₀ > 0`) at `ε₀ := 1/10/2` gives that premise: it is an instance of the already owed `BAGbEXPii` |
| D2 | S4 pin = `GreenMinor_diff_pin'` :228 (docstring: the S4 pin of G.8; the dispatcher clause is gone); `GreenMinor_diff_pin` :213 is the record; `example : ¬ GreenMinor_diff_pin` :770 unchanged | :459 (S2 + S4: `h4 : GreenMinor_diff_pin'`, hand datum `d = 3, L = 3, W = 2`, `κ = 1/2`, `l = [q]`); :657 at the carrier, every `n`: `1/2 ≤ ‖m‖ ≤ 1` at `sz0`, `flow_sz0` (`BAflow_real`, `BAm_norm_le_one`), i.e. `κ ≤ ‖m‖` and `κ ≤ 1` at `κ = 1/2` |
| D3 | `BAFamGain` :320 (compiled `Prop`) with the families `GreenMinor_famA` :303, `GreenMinor_famX` :310; `ρ = 4δ`, `B = Cδ`, `δ = W^τ Ψ_n`, `M = K = 2p`, `0 < τ ≤ ε₀/2`, `∀ p`, `∃ C ≥ 0` after the data and before `∀ᶠ n`, `A = Iblk d (sz.L n) (sz.W n) β`, `β ≠ α` | :739 same data as D1, `τ = 1/20`, `p = 1`; hypotheses left: `h : BAFamGain 3`, `hii` (G6's), the premise `STInitialGT2gL`; the `famGain` content is `h`, the conclusion is written out |
**Differences from the pseudo-Lean of (a′) D3** (each visible in the file): (1) `let G, M, D, s, m := …` and `fun x ω => GreenMinor_YA G M D s m x` are the two defs `GreenMinor_famA`, `GreenMinor_famX` (`GreenCore_Gc/Mc/Dc sz z n (t n) ω`, `s = E_n + m`, `m = BAmF`), indexed by the fine `k : Idx` through `split` (the `x` of the pseudo-Lean is `split k`; `y = (α, (split k).2)` for `Y^X`); (2) `A` is `Iblk` (the filter `(split k).1 = β`), as `mA` of the S5 instance (:673); (3) `δ` is written inline; (4) `famGain` is `GreenMinor_famGain` (:246) at `sz.withLam 0`, the law of `PrecL`. Not written: `ρ ≤ 1`, `c = W^{-d} ≤ ρ²` (they follow from the window, as (a′) D3 states).
**Not done here (open for the 1a-audit round 2):** the pins are statements; none is proved, and the truth of `BAFamGain` and of `GreenMinor_diff_pin'` rests on (a′) D2-D3 (the compiled facts are the instances above and `¬ GreenMinor_diff_pin`). `GreenMinor_famGain`, `GreenMinor_famAvg_moment_pin` (:246, :257) stay in the probe as G5b's vocabulary (D4).
Paper-delta candidates: none new in this step (`T2401d` unchanged; D1 adds none, `T2401-1a-audit.md` O5). Names used by the new examples (each compiled): `BAGbEXPii` `BA/Step1Boot.lean:108`, `BAflow_real` `BA/GreenSchur.lean:59`, `BAm_norm_le_one` `BA/Ward.lean:136`, `Complex.abs_im_le_norm` `Mathlib/Analysis/Complex/Norm.lean:187`, `Iblk` `Defs/Sizes.lean:92`, `split` `:64`. New public names `GreenMinor_famA`, `GreenMinor_famX`, `BAFamGain`: no clash (the `git grep` above, 0 hits on `main`).

## (b) Stage 1b: script output — Sun Oct 11 05:41:57 UTC 2026
Step role `prover-max` (claude-sonnet-5-5) under Amend 1 (H201, `docs/tickets/T2401-amend-1.md`); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2401`, branch `t/T2401`, HEAD `8104042`. Sections (a), (G), (a″), (a′), (a‴) are not edited. `main` (1c25de0) was merged into the branch first (dcb7382; 1a-audit O3). Scripts and verbatim outputs: `docs/reports/T2401/b_{targets,instances,defdiff}.py`, `b_{pincheck,axsum,names}.lean`, each with `.out`, and `b_fullbuild.out`. No port from RBM1D/RBM2D (no diff-stat); the twins of merged RBM3D files are named in the narrative.
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2401 && wc -l RBM3D/BA/GreenMinor.lean RBM3D/BA/GreenMinor2.lean RBM3D/BA/GreenMinor3.lean
     434 RBM3D/BA/GreenMinor.lean
     685 RBM3D/BA/GreenMinor2.lean
    1003 RBM3D/BA/GreenMinor3.lean
    2122 total
$ git diff --stat main...t/T2401        (RBM3D/Probe/T2401Pins.lean stays on the branch and is never merged)
 RBM3D.lean                 |    3 +
 RBM3D/BA/GreenMinor.lean   |  434 +++++++++++++++++++
 RBM3D/BA/GreenMinor2.lean  |  685 ++++++++++++++++++++++++++++++
 RBM3D/BA/GreenMinor3.lean  | 1003 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2401Pins.lean |  847 +++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |    2 +
 6 files changed, 2974 insertions(+)
$ lake build RBM3D.BA.GreenMinor RBM3D.BA.GreenMinor2 RBM3D.BA.GreenMinor3 2>&1 | tail -1        (05:41:57 UTC)
Build completed successfully (3784 jobs).
$ lake build        (full library, runs #assert_rbm_axioms; log summarised in docs/reports/T2401/b_fullbuild.out)
$ grep -v 'premises found\|registry: ' docs/reports/T2401/b_fullbuild.out
== full lake build at HEAD 8104042 (log: scratchpad fullbuild4.out; start and end from date -u):
start: Sun Oct 11 05:35:10 UTC 2026
end:   Sun Oct 11 05:35:57 UTC 2026
5147:info: RBM3D.lean:450:0: axiom audit: 11504 theorems, 3478 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
5240:  RBM.BA.BAFamGain: 0 [no certificate]
5241:  RBM.BA.BAFAav: 0 [no certificate]
5281: RBM.BA.BAFamGain,
5282: RBM.BA.BAFAav,
5362:Build completed successfully (4218 jobs).
5363:EXIT=0
lines of the log mentioning RBM3D/BA/GreenMinor (warnings): 0
$ grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide' RBM3D/BA/GreenMinor*.lean; echo grep-exit=$?
grep-exit=1
$ lake env lean docs/tickets/checks/T2401-check.lean; echo EXIT=$?
EXIT=0
$ sed 's/^RBM.BA.GreenMinor_//; s/: \[propext, Classical.choice, Quot.sound\]/ std/' docs/reports/T2401/b_axsum.out | paste -sd' ' - | fold -s -w 190      (b_axsum.out = `lake env lean docs/reports/T2401/b_axsum.lean`; `std` = [propext, Classical.choice, Quot.sound]; the per-target lines are in the file)
removal std cross std removal_crossL std removal_crossR std removal_cross std offset_ne: [propext] tower std tower_carrier std good_of_event std Arow_eq std Xrow_eq std split_A std split_X 
std YA_le std YX_le std diff std avgK_eq std avg_split std RBM.BA.BAFamGain std RBM.BA.BAFAav std declarations of the three files (theorems, definitions, structure): 141   132 with axioms 
[Classical.choice, Quot.sound, propext]   3 with axioms [Quot.sound, propext]   6 with axioms [propext]
```
**Target statements** (`python3 docs/reports/T2401/b_targets.py .`, text of each theorem up to `:=`; binders of the enclosing `variable` line, e.g. `{d L W} [NeZero L] [NeZero W] {G X D M} {Mb} {t g₀} {m s z}` in S3, are not in the extracted text; the next block compares the full types):
```
GreenMinor.lean:85: theorem GreenMinor_removal {d L W : ℕ} [NeZero L] [NeZero W] {G : Matrix (Vtx d L W) (Vtx d L W) ℂ} {κ : ℝ} {w : Vtx d L W} (hκ : 0 < κ) (hw : κ / 2 ≤ ‖G w w‖) (x y : Vtx d L W) : ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * ‖G x w‖ * ‖G w y‖
GreenMinor.lean:96: theorem GreenMinor_cross {d L W : ℕ} [NeZero L] [NeZero W] {M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) {x y : Vtx d L W} (h : x.2 ≠ y.2) : M x y = 0
GreenMinor.lean:102: theorem GreenMinor_removal_crossL {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {κ δ : ℝ} {w : Vtx d L W} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ) (hκ : 0 < κ) (hw : κ / 2 ≤ ‖G w w‖) (x y : Vtx d L W) (hxw : x.2 ≠ w.2) : ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ * ‖G w y‖
GreenMinor.lean:114: theorem GreenMinor_removal_crossR {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {κ δ : ℝ} {w : Vtx d L W} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ) (hκ : 0 < κ) (hw : κ / 2 ≤ ‖G w w‖) (x y : Vtx d L W) (hwy : w.2 ≠ y.2) : ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ * ‖G x w‖
GreenMinor.lean:127: theorem GreenMinor_removal_cross {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {κ δ : ℝ} {w : Vtx d L W} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ) (hκ : 0 < κ) (hw : κ / 2 ≤ ‖G w w‖) (x y : Vtx d L W) (hxw : x.2 ≠ w.2) (hwy : w.2 ≠ y.2) : ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ ^ 2
GreenMinor.lean:142: theorem GreenMinor_offset_ne {d L W : ℕ} [NeZero L] [NeZero W] {β : Zd d L} {o : Fin (W ^ d)} {w x : Vtx d L W} (hw : w ∈ GreenMinor_R β o) (hx : x ∈ GreenMinor_T β o) (hxw : x ≠ w) : x.2 ≠ w.2
GreenMinor.lean:286: theorem GreenMinor_tower {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) : GreenMinor_Tower (green H z) (GreenMinor_Gs H z)
GreenMinor.lean:314: theorem GreenMinor_tower_carrier {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) : GreenMinor_Tower (GreenCore_Gc sz z n t ω) (GreenMinor_Gs (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t))
GreenMinor2.lean:134: theorem GreenMinor_good_of_event (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m) (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (hδ0 : 0 ≤ δ) (hδ4 : 4 * δ ≤ κ) (hMδ : 8 * (m₀ : ℝ) * δ ≤ κ) (hT : GreenMinor_Tower G Gs) (hG : ∀ x y, ‖G x y - M x y‖ ≤ δ) (β : Zd d L) (o : Fin (W ^ d)) : GreenMinor_good Gs M κ δ m₀ β o
GreenMinor2.lean:206: theorem GreenMinor_Arow_eq (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1) (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m) (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m) (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hm : m ≠ 0) {u : Vtx d L W} (hG0 : G u u ≠ 0) : GreenCore_Arow G X D t m u = GreenMinor_YA G M D s m u * m / G u u
GreenMinor2.lean:226: theorem GreenMinor_Xrow_eq (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1) (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m) (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m) (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hm : m ≠ 0) {u y : Vtx d L W} (hG0 : G u u ≠ 0) (hyu : y ≠ u) : GreenCore_Xrow G X u y = -(GreenMinor_YX G M D s m u y * m / G u u)
GreenMinor2.lean:262: theorem GreenMinor_split_A (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1) (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m) (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m) (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hm : m ≠ 0) {u : Vtx d L W} (hG0 : G u u ≠ 0) : GreenCore_Arow G X D t m u = GreenMinor_YA G M D s m u - GreenCore_Arow G X D t m u * (G u u - m) / m
GreenMinor2.lean:274: theorem GreenMinor_split_X (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1) (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m) (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m) (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hm : m ≠ 0) {u y : Vtx d L W} (hG0 : G u u ≠ 0) (hyu : y ≠ u) : GreenCore_Xrow G X u y = -GreenMinor_YX G M D s m u y - GreenCore_Xrow G X u y * (G u u - m) / m
GreenMinor2.lean:303: theorem GreenMinor_YA_le (hL : 3 ≤ L) (hg : 0 ≤ g₀) (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ') (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (u : Vtx d L W) : ‖GreenMinor_YA G M D s m u‖ ≤ (‖s‖ + 2 * d * g₀) / κ * δ'
GreenMinor2.lean:321: theorem GreenMinor_YX_le (hL : 3 ≤ L) (hg : 0 ≤ g₀) (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ') (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (u y : Vtx d L W) (hMuy : ‖M u y‖ ≤ 1) : ‖GreenMinor_YX G M D s m u y‖ ≤ ((‖s‖ + 2 * d * g₀) * (1 / κ + 1) + 4 * d * g₀ * δ' / κ) * δ'
GreenMinor3.lean:691: theorem GreenMinor_diff {G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ} {s m : ℂ} {κ δ g₀ : ℝ} {m₀ : ℕ} {β : Zd d L} {o : Fin (W ^ d)} {u y : Vtx d L W} (hL : 3 ≤ L) (hg : 0 ≤ g₀) (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hm : κ ≤ ‖m‖) (hMuy : ‖M u y‖ ≤ 1) (hT : GreenMinor_Tower G Gs) (hgood : GreenMinor_good Gs M κ δ m₀ β o) (hu : u = (β, o)) (hy : y.2 = o ∧ y.1 ≠ β) (l : List (Vtx d L W)) (hl : l.Nodup) (hR : ∀ k ∈ l, k ∈ GreenMinor_R β o) (hlen : l.length ≤ m₀) (h2δ : 2 * δ ≤ 1) : ‖iterDeltaFam l (fun S => GreenMinor_YX (Gs S) M D s m u y) ∅‖ ≤ GreenMinor_cY d κ g₀ ‖s‖ l.length * (2 * δ) ^ (l.length + 1) ∧ ‖iterDeltaFam l (fun S => GreenMinor_YA (Gs S) M D s m u) ∅‖ ≤ GreenMinor_cY d κ g₀ ‖s‖ l.length * (2 * δ) ^ (l.length + 1)
GreenMinor3.lean:83: theorem GreenMinor_avgK_eq (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1) (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m) (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hG0 : ∀ u, G u u ≠ 0) (a : Zd d L) : GreenCore_vbar G M a - (t : ℂ) * ∑ b, Mb a b * Mb b a * GreenCore_vbar G M b = GreenMinor_avgK G M X D Mb t m a
GreenMinor3.lean:109: theorem GreenMinor_avg_split (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (a : Zd d L) : GreenMinor_avgK G M X D Mb t m a = ∑ b', Mb a b' * ((t : ℂ) * GreenCore_vbar G M b' * GreenMinor_avg (fun o : Fin (W ^ d) => G (b', o) (a, o) - M (b', o) (a, o)) - Mb b' a * GreenMinor_avg (fun o : Fin (W ^ d) => GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b') - GreenMinor_avg (fun o : Fin (W ^ d) => (GreenCore_Arow G X D t m (b', o) + (t : ℂ) * GreenCore_vbar G M b') * (G (b', o) (a, o) - M (b', o) (a, o))) - GreenMinor_avg (fun o : Fin (W ^ d) => GreenCore_Xrow G X (b', o) (a, o)))
```
**Statements against the pins** (`lake env lean docs/reports/T2401/b_pincheck.lean`: the 16 probe pins `GreenMinor_*_pin` copied from `RBM3D/Probe/T2401Pins.lean`, each followed by `example : <pin> := @<theorem>`; and `python3 docs/reports/T2401/b_defdiff.py .`):
```
$ lake env lean docs/reports/T2401/b_pincheck.lean; echo EXIT=$?   -> (no output) then EXIT=0
$ python3 docs/reports/T2401/b_defdiff.py . | tail -2   (15 pinned definitions compared by text with the probe: T, R, Tower, good, YA, YX, a, cY, famGain, famA, famX, BAFamGain, BAFAav, avg, avgK)
GreenMinor_avgK: identical
differences: 0
```
**Instances** (`python3 docs/reports/T2401/b_instances.py .`: each `example` of the three files and the targets it applies; all are in the file of the theorem they apply; the last is the S4 instance):
```
GreenMinor.lean:377: applies GreenMinor_removal
GreenMinor.lean:387: applies GreenMinor_cross
GreenMinor.lean:391: applies GreenMinor_removal_crossL, GreenMinor_removal_crossR, GreenMinor_removal_cross
GreenMinor.lean:412: applies GreenMinor_offset_ne
GreenMinor.lean:417: applies GreenMinor_tower
GreenMinor.lean:426: applies GreenMinor_tower_carrier
GreenMinor2.lean:591: applies GreenMinor_tower, GreenMinor_good_of_event, GreenMinor_YA_le, GreenMinor_YX_le
GreenMinor2.lean:625: applies GreenMinor_good_of_event
GreenMinor2.lean:630: applies GreenMinor_YA_le, GreenMinor_YX_le
GreenMinor2.lean:656: applies GreenMinor_Arow_eq, GreenMinor_Xrow_eq, GreenMinor_split_A, GreenMinor_split_X
GreenMinor3.lean:888: applies GreenMinor_avgK_eq, GreenMinor_avg_split
GreenMinor3.lean:915: applies (none)
GreenMinor3.lean:920: applies BAFAav
GreenMinor3.lean:938: applies BAFamGain
GreenMinor3.lean:973: applies GreenMinor_tower, GreenMinor_good_of_event, GreenMinor_diff
15 examples
$ sed -n 973,980p RBM3D/BA/GreenMinor3.lean
example :
    GreenMinor_Tower (green hH Complex.I) (GreenMinor_Gs hH Complex.I) ∧
    GreenMinor_good (GreenMinor_Gs hH Complex.I) hM (1 / 2) (1 / 100) 3 0 0 ∧
    green hH Complex.I hp hy - hM hp hy ≠ 0 ∧
    ‖iterDeltaFam [hq] (fun S => GreenMinor_YX (GreenMinor_Gs hH Complex.I S) hM hD hm hm hp hy) ∅‖ ≤
        GreenMinor_cY 3 (1 / 2) (1 / 10) ‖hm‖ [hq].length * (2 * (1 / 100)) ^ ([hq].length + 1) ∧
    ‖iterDeltaFam [hq] (fun S => GreenMinor_YA (GreenMinor_Gs hH Complex.I S) hM hD hm hm hp) ∅‖ ≤
        GreenMinor_cY 3 (1 / 2) (1 / 10) ‖hm‖ [hq].length * (2 * (1 / 100)) ^ ([hq].length + 1) := by
```
**Registry, name clash, new Mathlib names:**
```
$ git diff main...t/T2401 -- RBM3D.lean RBM3D/Test/Axioms.lean   (changed lines, cut at 110 chars)
+import RBM3D.BA.GreenMinor
+import RBM3D.BA.GreenMinor2
+import RBM3D.BA.GreenMinor3
+   `RBM.BA.BAFamGain, -- the family gain interface `famGain(Cδ_n, 4δ_n, 2p, 2p)` (`GreenMinor_famGain`, `BA/G
+   `RBM.BA.BAFAav, -- the averaged law `|W^{-d} Σ_o Σ_{b'} M^{(B)}_{ab'} 𝒦_{(b',o),(a,o)}| ≺ Ψ²` over the BA 
$ git --no-optional-locks grep -n -e GreenMinor -e BAFamGain -e BAFAav main -- RBM3D RBM3D.lean | wc -l      (main = d354b8d)
0
$ git log --oneline 1c25de0..main        (main moved after the branch merge; none of its files is one of ours)
d354b8d T2409: merge BA-L2c2a Graph/BAGGExp (baGGGamma_holds)
88cc0fa T2409: BA-L2c2a baGGGamma_holds, the GG expansion (B.20) with the D402 coefficient, as an identity of expectations
```
**Narrative** (every file:line below was read in this step)
1. Files: `BA/GreenMinor.lean` (434 lines): the vocabulary of G.8 (`GreenMinor_T/_R/_Tower/_good/_YA/_YX`), S1 with the structural fact, R1; `BA/GreenMinor2.lean` (685): S2, S3 and the instance data; `BA/GreenMinor3.lean` (1003): S4, S6, the registry definitions, the S4 instance. The (a′) estimates were 777/1037/1676, 463/718/1078, 576/864/1298 (lo/central/hi; central total 2619); the stop line 2,000 per file was not approached. Each 1b commit message (b9ac826 to 8104042) carries the `wc -l`.
2. Pins: each of the 16 G5a pins of the probe is a theorem of the same name without `_pin`; S4 `GreenMinor_diff` has the type of `GreenMinor_diff_pin'` (Amend 1 D2), and `GreenMinor_avgK_eq` is `GreenMinor_avgK_pin`. The check above elaborates `example : pin := @theorem` for all 16, so binders, hypotheses and conclusions are the pins'. No hypothesis was added, no statement weakened, no pinned signature changed. R1 has no probe pin; its statements are those of (a″) F4.
3. R1: `GreenMinor_Gs H z S` is the generic twin of `Green.greenSetMat` (`Green/MinorGoodLe.lean:261`); `GreenMinor_Gs_empty`, `GreenMinor_insertEquiv`, `GreenMinor_Gs_insert_apply` adapt `greenSetMat_empty_apply` (`:507`), `insertRowEquiv` (`:556`), `greenSetMat_insert_apply` (`:572`) to an arbitrary Hermitian `H`; the nonvanishing diagonal is `green_diag_ne_zero` (`Green/LDE.lean:809`).
4. S2: induction on `|S|` (`GreenMinor_good_aux`), `δ_j ≤ δ + 8jδ²/κ ≤ 2δ`, the recursion of (G.2); twin of `minorGoodLe_of_goodEvent` (`MinorGoodLe.lean:977`).
5. S3: `GreenMinor_Arow_mul` (`A_u G_{uu} = 1 + s G_{uu} - Σ_l D_{ul} G_{lu}`) from `GreenCore_E1` (`BA/GreenCore.lean:84`) and the rows of `(D + X - z) G = 1`, `M (D - s) = 1`; the base bounds use `GreenCore_Drow` (`:672`). The pinned hypothesis `hD` (and `g₀`) of the four identities is not used by the proofs of `GreenMinor_Arow_eq`, `GreenMinor_Xrow_eq` (the identities hold for every `D`) and is only passed on by the two splits; it stays because it is pinned.
6. S4: the levels are `Finset (GreenMinor_Rows β o)`, the type of the protected rows, so every level is protected; the atoms are the centred entries `GreenMinor_gE` and the inverses `GreenMinor_gI`, zero at removed indices, so `(4.9)` and the reciprocal rule hold at every level (`GreenMinor_gE_delta`, `GreenMinor_gI_delta`; only the inverse rule needs `G_{aa} ≠ 0`, from the good event). The calculus of `Green/MinorDiff.lean:103-398` (`DiffBd`, `.mul`, `.congr`, `.mono_*`) is used as is (generic in the index type); new: linearity of `iterDeltaFam` and `GreenMinor_DiffBd_add/_smul/_sum/_zero` (the sum rule of (a′)). `GreenMinor_diffBd_atom` is the twin of `diffBd_atom` (`MinorDiff.lean:570`) with `atomC` replaced by `GreenMinor_a` (`a_0 = 2/κ ≥ 2` for `κ ≤ 1`) and the admissible atom indices `GreenMinor_Adm` (offset `o`, or a row already removed): for a new row `k`, `M_{ak} = M_{kb} = 0` by `GreenMinor_offset_ne`. `Y^X`, `Y^A` are bounded by `GreenMinor_DiffBd_modelX/_modelA` with the constant `GreenMinor_cY` of (G.8) S4; `GreenMinor_iter_lev` carries the bound from `Finset R` levels to the pin's `iterDeltaFam l … ∅`. Route A of (G.5) only.
7. S6: `GreenMinor_avgK_eq` is the averaged `GreenCore_E3` (the argument of `GreenCore_coupled`, `GreenCore.lean:1291-1309`, as an identity); `GreenMinor_avg_split` is the algebra of `GreenCore_K` with `M_{(b',o)(a,o)} = M^{(B)}_{b'a}`.
8. Registry: `GreenMinor_famGain`, `_famA`, `_famX`, `BAFamGain`, `BAFAav` are definitions with the text of the probe (`b_defdiff`); by the 1a-audit O1 the three `def`s are in `GreenMinor3`. Two owed lines are added to `owedProps` (diff above); no theorem rests on them yet (`BAFamGain: 0`, `BAFAav: 0` in the build output).
9. Instances (every deterministic hypothesis discharged; other gates' pins stay hypotheses): (1) the hand datum `d=3, L=3, W=2`, `m=i`, `M=mI`, `Δ=ε(E_pq+E_qp)`, `ε=1/100`, `p=(0,0)`, `q=(0,1)`: S1, `offset_ne`, S2 and the S3 bounds with the explicit tower `hGs`; (2) the real resolvent `G=(H-i)⁻¹`, `H=ε 1_C 1_Cᵀ`, `C={p,q,y}`, `y=(e_0,0)`, `ε=1/100` (`G = iI + cJ_C` proved: `green_hH`): R1, S2 (`κ=1/2`, `δ=1/100`, `m₀=3`), the S3 bounds, and S4 at `u=p`, `l=[q]`, `g₀=1/10`, `s=m=i`, with `Δ_{py}=c≠0` proved; (3) the BA carrier `sz0` (`d=3`, `n=0`, `L=4`, `W=32`), `t=1/2`, every sample `ω`: R1 at the carrier, the four S3 identities, both halves of S6; `BAFAav`, `BAFamGain` at `ε₀=1/10`, `Ψ=W^{-1}`, `τ=1/20`, `p=1`, with `BAGiiGEX` at `ε₀/2` (an instance of the owed `BAGbEXPii`, `Step1Boot.lean:108`) and `STInitialGT2gL` as hypotheses.
10. Hygiene: every handwritten declaration of the three files has axioms within {propext, Classical.choice, Quot.sound}; unpinned helpers are prefixed `GreenMinor_` (rule (E)), the carrier abbreviations of the instance sections are `private`; no merged file is edited (`git diff --stat` above); the deprecated aliases `if_pos`, `if_neg`, `if_true`, `if_false`, `push_neg` do not occur in the three files.

## (c) Verified Mathlib names (module:line, from `lake env lean docs/reports/T2401/b_names.lean`; each occurs in the three files, `Matrix.IsHermitian.submatrix` as `hH.submatrix`)
```
Matrix.inv_submatrix_equiv  Mathlib.LinearAlgebra.Matrix.NonsingularInverse:721   |   Matrix.IsHermitian.submatrix  Mathlib.LinearAlgebra.Matrix.Hermitian:100   |   Matrix.nonsing_inv_mul  Mathlib.LinearAlgebra.Matrix.NonsingularInverse:215
Matrix.inv_eq_left_inv  Mathlib.LinearAlgebra.Matrix.NonsingularInverse:458   |   Matrix.isUnit_iff_isUnit_det  Mathlib.LinearAlgebra.Matrix.NonsingularInverse:126   |   mul_eq_one_comm  Mathlib.Algebra.Group.Monoid:54
Matrix.mul_eq_one_comm  ABSENT   |   Equiv.subtypeUnivEquiv  Mathlib.Logic.Equiv.Basic:345   |   Finset.notMem_empty  Mathlib.Data.Finset.Empty:107
Finset.insert_erase  Mathlib.Data.Finset.Basic:144   |   Finset.card_erase_of_mem  Mathlib.Data.Finset.Card:150   |   Finset.notMem_erase  Mathlib.Data.Finset.Erase:60
Finset.mem_of_mem_erase  Mathlib.Data.Finset.Erase:65   |   Finset.card_pos  Mathlib.Data.Finset.Card:78   |   Finset.map_insert  Mathlib.Data.Finset.Image:226
Finset.map_union  Mathlib.Data.Finset.Image:210   |   Finset.insert_union  Mathlib.Data.Finset.Lattice.Lemmas:80   |   Finset.union_insert  Mathlib.Data.Finset.Lattice.Lemmas:84
Finset.insert_eq_of_mem  Mathlib.Data.Finset.Insert:396   |   Finset.card_union_le  Mathlib.Data.Finset.Card:590   |   Finset.card_insert_le  Mathlib.Data.Finset.Card:109
Finset.subset_insert  Mathlib.Data.Finset.Insert:444   |   Finset.sum_boole  Mathlib.Algebra.BigOperators.Ring.Finset:44   |   Finset.filter_mem_eq_inter  Mathlib.Data.Finset.Basic:357
Finset.card_insert_of_notMem  Mathlib.Data.Finset.Card:103   |   Finset.sum_insert  Mathlib.Algebra.BigOperators.Group.Finset.Basic:48   |   Finset.sum_mul  Mathlib.Algebra.BigOperators.Ring.Finset:56
Finset.sum_comm  Mathlib.Algebra.BigOperators.Group.Finset.Sigma:120   |   List.pmap_cons  Init.Data.List.Attach:76   |   List.Nodup.pmap  Mathlib.Data.List.Nodup:224
List.length_pmap  Init.Data.List.Attach:197   |   List.nodup_cons  Init.Data.List.Pairwise:357   |   inv_anti₀  Mathlib.Algebra.Order.GroupWithZero.Basic:1220
div_le_div_of_nonneg_right  Mathlib.Algebra.Order.GroupWithZero.Basic:1193   |   div_le_div_of_nonneg_left  Mathlib.Algebra.Order.GroupWithZero.Basic:1270   |   one_div_le_one_div_of_le  Mathlib.Algebra.Order.Field.Basic:69
pow_le_pow_right₀  Mathlib.Algebra.Order.GroupWithZero.Basic:500   |   pow_le_pow_left₀  Mathlib.Algebra.Order.GroupWithZero.Basic:513   |   one_le_pow₀  Mathlib.Algebra.Order.GroupWithZero.Basic:484
norm_add₃_le  Mathlib.Analysis.Normed.Group.Basic:109   |   norm_sub_norm_le  Mathlib.Analysis.Normed.Group.Basic:757   |   Complex.abs_re_le_norm  Mathlib.Analysis.Complex.Norm:39
Complex.I_sq  Mathlib.Basic.Complex.Basic:625   |   Complex.I_mul_I  Mathlib.Basic.Complex.Basic:251   |   Complex.conj_ofReal  Mathlib.Basic.Complex.Basic:473
Complex.I_ne_zero  Mathlib.Basic.Complex.Basic:258   |   Real.rpow_le_rpow_of_exponent_le  Mathlib.Analysis.SpecialFunctions.Pow.Real:616   |   ite_true  Init.SimpLemmas:237
ite_false  Init.SimpLemmas:238   |   ite_eq_right_iff  Init.PropLemmas:794   |   not_or  Init.PropLemmas:149
```
Verified absent: `Matrix.mul_eq_one_comm` (the root `mul_eq_one_comm` is used). The deprecated aliases `if_pos`, `if_neg`, `if_true`, `if_false`, `push_neg` are not used; the files use `simp`, `ite_eq_right_iff`, `not_or`, `ite_true`, `ite_false` instead.

## (d) Open issues and paper-delta candidates
- **Not here, by Amend 1 D4 (G5b):** S5/R6. `GreenMinor_famGain` is only a definition (T2401b: the interface restricts word rows to the block `A`; `FlucGainUpTo'` is not a special case); `famAvg_moment` (the graded iteration, twin of `Green/FlucIterGain.lean:566-895`) is not proved. Also not provided: the independence of the carrier minors from the removed rows (`FinDepOffRows`; `RowIndep_submatrix_shift_congr`, `Green/RowIndep.lean:1341`) and the `BddMeas`/`FinDep` facts of the families `GreenMinor_famA`, `GreenMinor_famX`: `GreenMinor_tower_carrier` is the algebraic tower only.
- **Owed pins:** `BAFamGain`, `BAFAav` have no proof (owner BA-G5b, consumer BA-G6b) and carry nothing yet (`BAFamGain: 0`, `BAFAav: 0` above). Their premise `BAGiiGEX` at `ε₀/2` is an instance of the owed `BAGbEXPii` (`GreenMinor3.lean:915`).
- **Constants:** `GreenMinor_a` is Route A (`a_{r+1} = 16^r a_r^5`): the thresholds of G5b's `hB1` are `W ≥ 10^{33}`-`10^{91}` at `ε₀ = 1` ((a) table row 9; eventual in `n` only). Route B ((G.5), `c_m = 2m(m-1)^{m-1} q^m`) is not proved here; it would be a primed successor of `GreenMinor_cY`.
- **S4 and `κ ≤ 1`:** `GreenMinor_diff` needs it (T2401d; BA supplies it: `BAm_norm_le_one`, `BA/Ward.lean:136`); the displayed G.8 form without it is false (`example : ¬ GreenMinor_diff_pin`, `RBM3D/Probe/T2401Pins.lean:770`, compiled in (a″)/(a‴)); that form is not in the library.
- **Branch and merge:** `main` moved to `d354b8d` (T2409: `RBM3D/Graph/BAGGExp.lean` and one import line of `RBM3D.lean`) after the branch merge dcb7382; the hub unions `RBM3D.lean` at merge; the name-clash grep above ran against it (0 hits). `RBM3D/Probe/T2401Pins.lean` is on the branch (`git diff --name-only main...t/T2401` lists it) and must not be merged.
- **Length:** sections (a)-(a‴) of this report are 419 lines (1a-audit O2); this stage adds 153 lines (ticket: at most 200 for 1b).
- **Paper-delta candidates:** none new in 1b. T2401a (`BAFAav`: the averaged law for all `g ≤ Λ`), T2401b (`GreenMinor_famGain`: rows in the block), T2401c (`GreenMinor_a`: `a_0 = 2/κ`), T2401d (`GreenMinor_diff`: `κ ≤ 1`) are realised by the declarations in parentheses.
