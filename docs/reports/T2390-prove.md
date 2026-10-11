Prover model: claude-opus-5-5

# T2390 stage 1a: design gate for G3a / G3b / G4 (CONTROL H182). Mathematics only; no Lean was written in this stage.

Citations: `path:N` is relative to `RBM3D/` on `main` bf5f0d5; `7_8:N`, `1_2:N`, `3_5:N` are lines of `paper/tex/7_8_light_weight.tex`, `1_2_Intro_model_result.tex`, `3_5_Loop_Hierarchy.tex`. Scripts and verbatim outputs: `docs/reports/T2390/{stab,chk,consts}.py` and `*.out`.
Notation: site `u=(a,o)` (block `a∈Z_L^d`, offset `o`), `[u]=a`; `X=√t V` (in-block GUE, `E|X_uv|²=tW^{-d}`), `D=g₀Ψ` (off-block, same offset), `H=D+X`, `z=z_t`, `G=(H-z)⁻¹`, `M=M^{(B)}⊗I`, `m=m₀=M_uu`, `Δ=G-M`, `G^{(u)}` the minor, `N(u)` the `2d` same-offset neighbours of `u`, `‖·‖` the max norm.

## (a) Math preflight — Sat Oct 10 13:27:24 UTC 2026

### (i) Exponent table
Instance data `d=3, L=4, W=32, N=2097152, ε=1/10, 𝔠=1/6, 𝔡=1/10 (Λ=10)`, `g=λ∈{1/64,1,10}`, `w=iη` (η=1.2,1.2,1.0), `z=w-m_S(w)`; `L→∞` means `L=256` (g=10), `L=96` (g=1), `L=64` (g=1/64).

| quantity | value (g = 1/64 / 1 / 10) | constraint | slack |
|---|---|---|---|
| `Admissible` (`BAFlow.1`) | `W=32 ≥ N^{1/6}=11.31`; `W^{-d/2+𝔡}=7.8e-3` | `W ≥ N^{1/6}`; `W^{-d/2+𝔡} ≤ g ≤ 𝔡⁻¹` | 2.8×; `g/W^{-d/2+𝔡}`=2.0× / 128× / 1280×; `Λ/g`=640× / 10× / 1.0× (equality `g=Λ` at g=10) |
| `g₀=√t₀ g` (L=4) | 0.0130 / 0.5610 / 4.6723 | `0<g₀≤Λ=10` (`BAflow_lam0_window`, `GreenSchur.lean:72`) | 770× / 17.8× / 2.14× |
| `Im m(z)` (L=4) | 0.8325 / 0.3777 / 0.2620 | `κ ≤ Im m(z)` (`BAdom`, `MFixedPoint.lean:435`) | κ=0.5/0.25/0.25: 1.67× / 1.51× / 1.05× |
| `Im m(z)` (L→∞, same `w`) | 0.8325 / 0.3435 / 0.0439 | `κ ≤ Im m(z)` **uniformly in L** | κ=0.5/0.25/**0.04**: 1.67× / 1.37× / 1.10× |
| `Im z` (L→∞) | 0.368 / 0.857 / 0.956 | `N^{-1+ε} ≤ Im z ≤ 1` (`BAdom`) | 0.044 at g=10; `w=1.2i` at g=10 gives `Im z=1.083` (L=8) … `1.156` (L=128) `>1`: not in `BAdom` |
| `t₀=Im m/(Im m+Im z)` (L→∞) | 0.6937 / 0.2862 / 0.0439 | `0 ≤ t ≤ t₀ < 1` | `1-t₀ ≥ 0.956`; stability tested up to `t=1` |
| `Im m₀=Im m/√t₀`, `|m₀|≤1` | 0.9995 / 0.642 / 0.2095 | `κ ≤ Im m₀`, `‖m₀‖≤1` (Ward) | ≥ 2.0× / 2.6× / 5.2× |
| rate `c=BAct_rate(3,10,κ)` | 4.158e-3 / 2.081e-3 / 3.33e-4 | `‖M_xy‖ ≤ c⁻¹e^{-c|x-y|}` | `max‖M‖/(c⁻¹e^{-c|b|})=4e-3 / 1e-3 / 7e-5` (≤1) |
| observed decay rate of `M_{0b}` | 3.41 / 0.25 / 0.053 | `> c` | 820× / 120× / 160× |
| `ρ=Σ_b|M_{0b}|` observed | 1.083 / 15.9 / 521 | `≤ c⁻¹expC(1,c)` (`BAMfine_row_l1`) | analytic 4.9e15 / 1.6e17 / 1.5e21 |
| `ρ₂=max Σ_b|M_ab||M_bc|` | 1.000 / 1.000 / 1.000 | `≤ 1` (Ward + Cauchy–Schwarz) | 0 (equality at `a=c`) |
| `‖Θ_t‖_{∞→∞}`, `t∈{0,t₀/2,t₀,1}` | ≤1.00 / ≤1.02 / ≤1.68 | `≤ 4/(κ²|1-tm₀²|) ≤ 16κ⁻⁴` | `16κ⁻⁴`=256 / 4096 / 6.25e6 (κ=0.5/0.25/0.04) vs observed ≤1.68 |
| `min_p|1-tσ̂(p)|` at `t=1` | 1.998 / 1.272 / 0.988 | `>0` uniformly | no degeneration at `t↑1`, hence none at `t↑T₀` |
| `K_BA=ρ(1+tρ₂‖Θ‖)` observed, `t=1`, L→∞ | 1.62 / 30.9 / 1355 | bounded in `L` | at g=10: 713, 1164, 1355 at L=64,128,256: saturating |
| `K_BA` analytic `ρ(1+16κ⁻⁴)` | 1.3e18 / 6.5e20 / 9.3e27 | finite, `(d,κ,𝔡)` only | not used at the instance (see (ii)) |
| `δ=W^{-ε₀}`, `ε₀=1` | 1/32 | `K_BA δ ≤ 1/2`; `δ ≤ κ/2` (`|G_uu| ≥ κ-δ`) | observed K at L=4: 0.051 / 0.349 / 0.320; `δ ≤ κ/2`: 8× / 4× / 4× |
| same, analytic `K_BA` | — | `log₁₀W ≥ log₁₀(2K_BA)/ε₀` | 18.4 / 21.1 / 28.3 (ε₀=1): eventual in `n` only |
| `Φ` (LDE factor `N^τ`) | 3 | `Φ ≥ 1`, `36Φδ² ≤ 1` | 0.105: 9.5× |
| `ε₀` window of `Ψ` | `[W^{-3/2},W^{-ε₀}]=[5.5e-3,3.1e-2]` | nonempty iff `ε₀ ≤ d/2` | 1.5× |
| `|N(u)|=2d`, coefficient of `Q^{XD}` | 6, `2d g₀ ≤ 2dΛ=60` | independent of `L,W` | — |
| `c_λ=½min(BAct_rate,BAp5s_rate)=μ/2` | 6.5e-33 / 4.9e-38 / 1.5e-51 (`μ=1.3e-32 / 9.9e-38 / 2.9e-51`) | `>0`, `(d,κ,𝔡)` only | existence only |
| window constant of `flowFM_wl_det` (`Step1Setup.lean:125`, docstring `:112`) | old `2·9^d+1=1459` | new `3·expC(d-2,c_λ)⁴+4` | independent of `n` |

### (ii) One concrete nondegenerate instance
`d=3, L=4, W=32` (`N=2097152`), `(κ,ε,𝔠,𝔡)=(½|¼|¼, 1/10, 1/6, 1/10)` at `g=1/64|1|10`; `t∈{0,t₀/2,t₀}`; `ε₀=1`, `δ=1/32`, `Φ=3`; `Ψ=W^{-1}`. Hypotheses of the G3a/G3b statements: `BAFlow` (Admissible, `BAdom`), `BAReal`, `0<g₀≤Λ`, `t≤t₀<1`, `Kδ≤1/2`, `δ≤κ/2`, `36Φδ²≤1`, window nonempty, Ward, decay. The observed `K` replaces the analytic one in the instance (the analytic `K_BA` forces `W≥10^{18}`). Command and output:
```
python3 docs/reports/T2390/consts.py     (lines 6-9 of the output; lines 1-4 = analytic constants of the table; last block = diagonal-dominance check)
N = 2097152, N^(-1+eps) = 2.04e-06, N^(1/6) = 11.31 <= W: True; window [W^-3/2, W^-eps0] = [5.524e-03, 3.125e-02] nonempty: True
g=0.015625 kappa=0.5: Im m(z)=0.8325>=kappa True; N^(-1+eps)<=Im z=0.368<=1 True; Admissible W^(-d/2+dd)<=g<=1/dd True; g0=0.0130<=Lam True; t in [0, t0=0.6937]<1; |m0|<=1 True; kappa<=Im m0=0.9995 True; observed Kstab(t<=1) = 1.62: K*delta = 0.051 <= 1/2 True; delta <= kappa/2 True; 36*Phi*delta^2 = 0.105 <= 1 True; min_t gap = 1.000; Ward err 0e+00
g=1 kappa=0.25: Im m(z)=0.3777>=kappa True; N^(-1+eps)<=Im z=0.822<=1 True; Admissible W^(-d/2+dd)<=g<=1/dd True; g0=0.5610<=Lam True; t in [0, t0=0.3148]<1; |m0|<=1 True; kappa<=Im m0=0.6732 True; observed Kstab(t<=1) = 11.17: K*delta = 0.349 <= 1/2 True; delta <= kappa/2 True; 36*Phi*delta^2 = 0.105 <= 1 True; min_t gap = 1.000; Ward err 1e-15
g=10 kappa=0.25: Im m(z)=0.2620>=kappa True; N^(-1+eps)<=Im z=0.938<=1 True; Admissible W^(-d/2+dd)<=g<=1/dd True; g0=4.6723<=Lam True; t in [0, t0=0.2183]<1; |m0|<=1 True; kappa<=Im m0=0.5607 True; observed Kstab(t<=1) = 10.24: K*delta = 0.320 <= 1/2 True; delta <= kappa/2 True; 36*Phi*delta^2 = 0.105 <= 1 True; min_t gap = 1.000; Ward err 2e-15
```
Stability and decay versus `L` (command `python3 docs/reports/T2390/stab.py table`; full output `stab_table.out`; `rate=nan`: fewer than 2 shells; `dec` = `max|M|/(c⁻¹e^{-c|b|})`):
```
--- g = 0.015625, w = 1.2i, kappa = 0.5, Lean c = 0.004158 ---
L=  4 BAdom=True  Imz=0.368 Imm=0.8325 t0=0.6937 g0=0.0130 rho1=   1.08 K(t0)=   1.53 K(1)=    1.62 gap(1)=1.998 Th1(1)=0.501 rate=nan dec=4e-03
L= 64 BAdom=True  Imz=0.368 Imm=0.8325 t0=0.6937 g0=0.0130 rho1=   1.08 K(t0)=   1.53 K(1)=    1.62 gap(1)=1.998 Th1(1)=0.501 rate=3.412 dec=4e-03
--- g = 1, w = 1.2i, kappa = 0.25, Lean c = 0.002081 ---
L=  4 BAdom=True  Imz=0.822 Imm=0.3777 t0=0.3148 g0=0.5610 rho1=   5.92 K(t0)=   7.76 K(1)=   11.17 gap(1)=1.289 Th1(1)=0.889 rate=nan dec=1e-03
L= 16 BAdom=True  Imz=0.857 Imm=0.3435 t0=0.2862 g0=0.5350 rho1=  15.14 K(t0)=  19.54 K(1)=   29.41 gap(1)=1.272 Th1(1)=0.942 rate=0.309 dec=1e-03
L= 96 BAdom=True  Imz=0.857 Imm=0.3435 t0=0.2862 g0=0.5350 rho1=  15.91 K(t0)=  20.53 K(1)=   30.89 gap(1)=1.272 Th1(1)=0.942 rate=0.246 dec=1e-03
--- g = 10, w = 1.0i, kappa = 0.04, Lean c = 0.000333 ---
L=  4 BAdom=True  Imz=0.686 Imm=0.3138 t0=0.3138 g0=5.6017 rho1=   4.79 K(t0)=   6.40 K(1)=   10.12 gap(1)=1.004 Th1(1)=1.114 rate=nan dec=2e-04
L= 16 BAdom=True  Imz=0.940 Imm=0.0604 t0=0.0604 g0=2.4575 rho1=  43.55 K(t0)=  46.31 K(1)=  115.30 gap(1)=0.988 Th1(1)=1.648 rate=0.080 dec=8e-05
L= 64 BAdom=True  Imz=0.956 Imm=0.0442 t0=0.0442 g0=2.1024 rho1= 271.92 K(t0)= 284.41 K(1)=  713.19 gap(1)=1.018 Th1(1)=1.623 rate=0.057 dec=7e-05
L=256 BAdom=True  Imz=0.956 Imm=0.0439 t0=0.0439 g0=2.0953 rho1= 520.96 K(t0)= 544.71 K(1)= 1354.99 gap(1)=1.021 Th1(1)=1.601 rate=0.053 dec=7e-05
```
Real-axis family `(g₀,E)` with `Im m₀ ≥ κ_thr`, worst over an `E` grid, `t=1` (`stab.py scan`, `stab_scan.out`; selected lines):
```
g0=0.561   L=64 kappa_thr=0.25  #E= 40 max rho1=   26.89 min gap(1)=0.905 max ||Th||_1=1.457 max K(1)=    66.05 max ward err=7e-16
g0=4.6723  L=64 kappa_thr=0.05  #E= 30 max rho1=  439.92 min gap(1)=0.850 max ||Th||_1=1.994 max K(1)=  1316.98 max ward err=4e-16
g0=10.0    L=64 kappa_thr=0.05  #E=  6 max rho1=  442.65 min gap(1)=0.985 max ||Th||_1=1.995 max K(1)=  1321.72 max ward err=4e-16
```
At `g₀=4.6723` and `g₀=10` no `E` has `Im m₀≥0.25` at `L=32, 64` (`stab_scan.out`: `no E with Im m0 >= thr`).
External hypothesis `BALDEin` (T2389's pin: row, column, quadratic, diagonal LDE for `X` against minors of `G_t`): finite-size computation (not a limit), `d=3, L=3, W=2, N=216`, `g=1` design flow data, `t=0.9t₀`, 3000 samples (`python3 docs/reports/T2390/chk.py`, `chk.out`):
```
(e) LDE inputs, 3000 samples, u = 0 (block 0, offset 0), t = 0.323  [ratios are the factor Phi of hLrow, hLcol, hLquad, hLdiag]
  row   y in [u], y != u                        : E|LHS|^2 / E RHS = 0.328;  99.9% quantile of |LHS|^2/RHS = 2.02
  row   y = same offset, adjacent block         : E|LHS|^2 / E RHS = 0.329;  99.9% quantile of |LHS|^2/RHS = 2.25
  col   y = other offset, other block           : E|LHS|^2 / E RHS = 0.318;  99.9% quantile of |LHS|^2/RHS = 2.42
  quad  (Q^XX - t sum S G^{(u)}_kk)             : E|LHS|^2 / E RHS = 0.112;  99.9% quantile of |LHS|^2/RHS = 1.87
  diag  |X_uu|^2 vs S_uu                        : E|LHS|^2 / E RHS = 0.323;  99.9% quantile of |LHS|^2/RHS = 3.01
```
(`E|LHS|²/E RHS ≈ t`: the exact moment identity, `RHS` carries `S=W^{-d}1_{[u]}`, not `tS`.) Verdicts of section (a): **G3a PASS, G3b PASS, G4 PASS** (hypothesis sets nonempty at the numbers above; the exponents close; the only gap is the one stated in (G.9) R1: the compile of the primed pins).

## (G) Design gate: the BA argument for G3a / G3b / G4 (C1: only uniform facts are used)

### G.1 Merged facts used (file:line, all checked present)
Kronecker `M_xy=1_{o(x)=o(y)}M^{(B)}_{[x][y]}`: `BAMres_fine_apply` `FlowPins.lean:101`, `BAMfine_eq` `GreenSchur.lean:93`; in-block zero `BAPsiI_inBlock` `:265` (and `BAMfine_block_zero`, probe 126); `‖M_xy‖≤1` `:105`; decay `BAMfine_decay` `:124`, `BAMB_decay_large` `CombesThomas.lean:509`; `ℓ¹` rows `BAMB_row_l1` `:139`, `BAMfine_row_l1` `:173`; Ward rows `BAMB_ward_row` `Ward.lean:108`, `BAMB_row_sq_real` `:125`, symmetry `BAMB_symm` `:83`, `M_aa=m` `BAMB_diag_eq` `:89`, `|m|≤1` `:136`; `BAoffDiag_scalar` `:202`; `BAMss_ss_diag` `Prop5Short.lean:110`, `BAMss_row_offdiag_sum` `:121`; `baProp5s_holds` `:667`; resolvent identity `BAGt_sub_BAMfine` `GreenSchur.lean:219`; Schur splits `green_diag_split` `:293`, `green_off_split` `:335`; column Schur `sum_minorGreen_col` `Green/EntryCore.lean:153`; flow data `BAflow_real` `GreenSchur.lean:59`, `BAflow_lam0_window` `:72`. No other input.

### G.2 (i) Stability of the coupled system
Exact identities with `Y=X+tm` (algebra, no probability; `chk.out` (a)-(d), (b'), (c'): residuals ≤ 4e-15 at `N=216`):
- (E0) `Δ=-MYG=-GYM` (`BAGt_sub_BAMfine`).
- (E1) `(YG)_{uy}=A_u G_{uy}+𝔛_{uy}1_{u≠y}`, `A_u=tm+X_uu-Q^{XX}_u-Q^{XD}_u`, `𝔛_{uy}=Σ_{v∈[u]\u}X_uv G^{(u)}_{vy}`, `Q^{XX}_u=Σ_{v,k∈[u]\u}X_uv G^{(u)}_{vk}X_ku`, `Q^{XD}_u=g₀Σ_{l∈N(u)}𝔛_{ul}`. Proof: write `G_vy=G^{(u)}_{vy}+G_vuG_uy/G_uu` in `Σ_vX_uvG_vy` and `G_vu=-G_uuΣ_kG^{(u)}_{vk}H_ku` (column Schur). Column twin (E1'): `(GY)_{vw}=G_vwA'_w+𝔛'_{vw}`, `𝔛'_{vw}=Σ_{k∈[w]\w}G^{(w)}_{vk}X_kw` (checked, (b')).
- (E2) `A_u=-t v̄_{[u]}+ε_u+X_uu-Q^{XD}_u`, `v̄_a=W^{-d}Σ_{k∈a}Δ_kk`, `ε_u=-(Q^{XX}_u-tW^{-d}Σ_{k∈[u]\u}G^{(u)}_{kk})+tW^{-d}(G_uu+Σ_{k∈[u]\u}G_kuG_uk/G_uu)`.
- (E3) `Δ=M 𝒮[Δ] M+M𝒦`, `𝒮[R]=tΣ_a⟨R⟩_aP_a` (`⟨R⟩_a=W^{-d}Σ_{k∈a}R_kk`), `𝒦_{uy}=t v̄_{[u]}Δ_{uy}-(ε_u+X_uu-Q^{XD}_u)G_{uy}-𝔛_{uy}1_{u≠y}`.

Reading of the system: the unknowns are the block averages `v̄_a` of the diagonal (the only part of `Δ` that `𝒮` sees) and the entries `Δ_xy`. The diagonal feeds the off-diagonal through `M v̄ M` (E3); the off-diagonal feeds `𝒦` through `𝔛_{ul}` (`l∈N(u)`: the mixed term `Σ_kX_ik(G^{(i)}D)_{ki}` of T2378 §3) and `ε_u`. The term `(DG^{(i)}D)_ii` of T2378 §3 does not appear: it is part of `M`'s own Schur equation, absorbed by (E0).
**Stability operator** `ℬ[R]=R-M𝒮[R]M`. Since `(MP_bM)_{xy}=1_{o(x)=o(y)}M_{[x]b}M_{b[y]}` (Kronecker), `ℬ` acts on block vectors as `1-tM^{(+,+)}`, `M^{(+,+)}_{ab}=M^{(B)}_{ab}M^{(B)}_{ba}=(M^{(B)}_{ab})²` (Hadamard square, `BAMss true true`), replacing the scalar `1-tm²S`. Inverse: `Δ=M𝒦+M(Σ_bw_bP_b)M`, `w=tΘ_t⟨M𝒦⟩`, `Θ_t=(1-tM^{(+,+)})⁻¹=BATheta … t true true`.
**Inverse bound, identified with merged bounds.**
- (S1) max→max, no `g`, no `Λ`: if `|v_a-tΣ_b(M_ab)²v_b|≤B` for all `a`, then `‖v‖≤4B/(κ²|1-tm²|)≤16κ⁻⁴B`. Proof: `M^{(++)}_aa=m²` (`BAMss_ss_diag`), `Σ_{b≠a}|M^{(++)}_ab|=1-|m|²` (`BAMss_row_offdiag_sum`), and `BAoffDiag_scalar` gives `κ²/4≤|1-tm²|`, `1-|m|²≤(1-κ²/4)|1-tm²|` for `t∈[0,1]`; evaluate at a maximum of `|v|`. This is the BA analogue of `Stable S ξ K` (`Green/EntryCore.lean:911`; here a complex kernel `(M_ab)²` instead of `S`, `ξ=t`) with `K_Θ=16κ⁻⁴` (the role of `Kstab3`, `Green/Stability.lean:212`, which depends on `Λ`). Checked: `‖Θ_t‖≤4/(κ²|1-tm₀²|)` at the three points (`consts.out`, last block).
- (S2) localisation (for G4 only): `|Θ_{t,0a}|≤C₅(1_{a=0}+g₀²e^{-μ|a|})`, `t<1`, `g₀≤Λ` (`baProp5s_holds`); translation invariance exists only as a private lemma (`baP8_BATheta_shift`, `Prop6Path.lean:497`): G3b republishes it.
- (S3) `ρ:=sup_xΣ_y|M_xy|≤c⁻¹expC(d-2,c)` (`BAMfine_row_l1`), `ρ₂:=sup Σ_b|M_ab||M_bc|≤1` (Ward, Cauchy–Schwarz, `BAMB_symm`).
- Consequence: `‖Δ‖≤K_BA‖𝒦‖`, `K_BA=ρ(1+ρ₂K_Θ)`: `|(M𝒦)_xy|≤ρ‖𝒦‖`, `|⟨M𝒦⟩_b|≤ρ‖𝒦‖`, (S1) on `w-tM^{(++)}w=t⟨M𝒦⟩` gives `‖w‖≤K_Θρ‖𝒦‖`, and `|(MwM)_xy|≤ρ₂‖w‖`. Checked (`chk.out` (d)): `‖Δ‖=0.322≤K_BA‖𝒦‖=2.46`; the formula reproduces `Δ` to 4e-15.

### G.3 (ii) Entrywise law and in-block minors (G3a)
- Band map: (4.7), (4.8) are the Schur splits (E1), merged; (4.9) is the generic minor identity; (4.10)/(4.11) are the two-sided inequality below; (4.3) is the diagonal law below; (4.2) are the four LDE inputs `BALDEin` (hypotheses, row/col/quad/diag; `Q^{XD}` is a sum of `2d` row sums, so no fifth input).
- LDE bounds (`Φ=N^τ`): `|𝔛_uy|²≤ΦW^{-d}Σ_{v∈[u]\u}|G^{(u)}_vy|²`; `|Q^{XD}_u|²≤2d g₀²Σ_{l∈N(u)}|𝔛_ul|²`; `|Q^{XX}_u-tW^{-d}Σ_kG^{(u)}_kk|²≤ΦW^{-2d}Σ_{v,k∈[u]\u}|G^{(u)}_vk|²` (the right sides are those of `ldeRowRHS`, `ldeQuadRHS` at `S=svar 0`, without `t`); `|X_uu|²≤ΦW^{-d}`. Minors: `G^{(u)}_{vy}=G_vy-G_vuG_uy/G_uu`, `|G_uu|≥κ-δ≥κ/2` on `Ω={‖Δ‖≤δ}`.
- Two-sided inequality (the BA (4.10)): for the row-block average `R_{a,y}=W^{-d}Σ_{v∈a}|G_vy|²`, use `Δ_vy=-Σ_w(GY)_{vw}M_{wy}` and (E1'): `R_{a,y}≤C[ΦρΣ_{b'}|M_{b'[y]}|𝓛^{(2)}_{(−,+),(a,b')}+W^{-d}|M_{a[y]}|²+(ρδ)²sup R]`. The average over `v∈a` leaves one site with `M_vw≠0` (the one at the offset of `w`): this is the factor `W^{-d}`. Closes for `ρδ≤1/4`. Then `|𝔛_uy|²≲Φ𝓛`-weighted sums, i.e. `𝒦` is controlled by loops. `𝓛^{(2)}_{(a,b)}=W^{-2d}Σ_{x∈a,y∈b}|G_xy|²` (`1_2:78`).
- Diagonal law (BA (4.3)): on `Ω` with `K_BAδ≤1/2`: `‖Δ‖²≤C₂K_BA²Φ(max_{a,b}𝓛^{(2)}_{(−,+),(a,b)}+W^{-d})`, and `W^{-d}≤4κ⁻²max𝓛` because `𝓛_{(a,a)}≥W^{-d}avg|G_xx|²≥W^{-d}κ²/4`. This is the old pin `BAGbEXPii` (`1_Ω‖G-M‖²_max ≺ max𝓛`, all pairs): it follows from the same argument, so it needs no re-pin (G.7).
- Where `M` is not scalar: (a) `ℬ` (G.2); (b) `𝒦` contains multiples of `M_uy`: `X_uuM_uy`, `ε_uM_uy`, and the `M`-part `W^{-d/2}|M^{(B)}_{[u][y]}|` of `𝔛_uy`; they produce the term `Ψ_te^{-c|a-b|}`; (c) `|G_uu|≥κ-δ`.
- In-block minors / fluctuation averaging (G5a, G5b; reading, not verified here). Structural fact (Lean-checkable by `BAMfine_eq`): two distinct sites `u≠u'` of one block have different offsets, so `M_{ku'}=0` for every `k∈[u]∪N(u)` other than `u'` (`k∈[u]\u'`: a different offset; `k∈N(u)`: offset `o(u)≠o(u')`). Every removal difference `G_{ku'}G_{u'l}/G_{u'u'}` met in `(1-𝔼_u)Q_u`, `Q^{XX},Q^{XD}` is a product of cross-offset entries, which are `Δ`-entries (`M=0`), `O(Ψ)`: one factor `Ψ` per removed site, as in the band. `Q^{DD}` has no randomness over row `u` (`G^{(u)}` is independent of it). The sums are over one block (`S^{(B)}(0)=I`); the inter-block coupling enters only through `ℬ`, after averaging. The band gain survives for this reason.

### G.4 (iii) Off-diagonal decay (G4, `(GijGEX_BA)` `7_8:1940-1946`)
- The re-entry series `G_ij=-G_ii(Σ_{k∈[i]}X_ikG^{(i)}_kj+g₀Σ_{k∈N(i)}G^{(i)}_{kj})` has ratio `~2dg₀|G_ii|`, not small (`g₀` up to 10): it is resummed exactly by `M` (E0). What remains is the random re-entry `A'_u:=ε_u+X_uu-Q^{XD}_u` (small) and the quadratic term `tv̄Δ`.
- Split `𝒦=𝒦₀+𝒬`, `𝒦₀_{uy}=-A'_uM_{uy}-𝔛_{uy}1_{u≠y}`, `𝒬_{uy}=tv̄_{[u]}Δ_{uy}-A'_uΔ_{uy}`. Linear part, explicit solution (E3): `Δ^{(0)}_xy=Σ_{b'}M_{ab'}𝒦₀_{u_{b'}(x)y}+Σ_{b''}M_{ab''}w_{b''}M_{b''c}`, `w=tΘ⟨M𝒦₀⟩`; `Θ` decays (S2), `M` decays; with `|a-b'|≤|a-b''|+|b''-b|+|b-b'|` this is `≤Σ_{a',b'}max𝒦₀(a',b')e^{-c_λ(|a'-a|+|b'-c|)}`. With `|𝒦₀(a',b')|≲Φ(a',b')+W^{-d/2}|M_{a'b'}|` (G.3) this is `Σ_{a',b'}Φ_t(a',b')e^{-c_λ(|a'-a|+|b'-b|)}+Ψ_te^{-c_λ|a-b|}`; the `Ψ_t` term needs only `Ψ_t≥W^{-d/2}`. Quadratic part: absorbed in the weighted norm `sup_{x,y}e^{ν|[x]-[y]|}|Δ_xy|` (`ν=c/2`) by `K_{BA,ν}δ≤1/2`, `K_{BA,ν}=ρ_ν(1+ρ_{2,ν}K_Θ)`, `ρ_ν=Σ_b|M_ab|e^{ν|a-b|}≤c⁻¹expC(d-2,c-ν)`. `c_λ=½min(BAct_rate,BAp5s_rate)`.
- No step uses `g≤W^{-ε}`, smallness of `‖M-m₀I‖`, or `(Cλ)^{|a-b|}` (C1): `g₀≤Λ` enters only through `ρ`, `2dg₀≤60` and `BAMfine_decay`.

### G.5 (iv) Constants
All depend on `(d,κ,𝔡)` through `c=BAct_rate d 𝔡⁻¹ κ` (`CombesThomas.lean:45`) and `κ≤Im m₀`: `ρ=c⁻¹expC(d-2,c)`, `ρ₂≤1`, `K_Θ=16κ⁻⁴`, `K_BA=ρ(1+K_Θ)`, `c_λ`, `S=expC(d-2,c_λ)`, `2d`, `Λ=𝔡⁻¹`; `Φ=N^τ`, `δ=W^{-ε₀}` and the closure thresholds are eventual in `n`. **Finding (κ):** `κ` must come from `Im m(z)` uniformly in `L`: at `g=𝔡⁻¹=10` it is 0.262 at `L=4` (the design's table) but 0.0439 at `L≥64` with `Im z≤1` (table above); `κ=1/4` there is a finite-size value. The constants are then `K_BA≈1.4e3` (observed) instead of `10`.

### G.6 (v) Numeric check (outputs in (ii))
Both constants stay bounded in `L` at each `g`: `K_BA(1)=1.62` (g=1/64, constant in `L`), `30.9` (g=1, flat from `L=64`), `1355` (g=10, `κ=0.04`: 713, 1164, 1355 at `L=64,128,256`, saturating as `ρ` does with correlation length `1/0.053≈19`). The decay rates are `3.41, 0.25, 0.053`, all above `c`. `min_p|1-tσ̂|` at `t=1` is ≥0.988 on the chain family and ≥0.75 in the scan (`κ_thr≥0.05`): no degeneration as `t↑T₀`. Boundedness in `L` is the merged `BAMfine_row_l1` (uniform in `L`); the numerics show the saturation, not a growth without bound. The real-axis scan (fixed `κ_thr`, `E` grid, `L=32,64`) gives the same picture (`K` ≤ 66 at `g₀=0.561`; ≤ 1322 at `κ_thr=0.05`, `g₀=4.67,10`, still growing from `L=32` to `64`, as for the chain). Stop condition of the ticket: not triggered.

### G.7 (vi) The Lean form of the primed pins (specification in mathematics; not compiled, see R1)
- `BAGbEXPij'(d)`: `∀κ,ε,𝔡>0 ∃c_λ>0` (`d,κ,𝔡` only) `∀𝔠,sz,z` with `BAFlow`, `∀t` with `0≤t_n≤BAflowT0`, `∀ε₀>0`, `∀D>0`, for every deterministic `Φ_n(a,b)∈(0,W^{-ε₀}]` and `Ψ_n∈[W^{-d/2},W^{-ε₀}]`: if `1_Ω·𝓛^{(2)}_{t,(−,+),(a,b)}≺Φ_n(a,b)²` (uniformly in `(a,b)`, per-sequence `PrecL` as `BAGijGEX`, `Step1Boot.lean:88`), then `1_Ω|(G_t-M)_{xy}|≺Σ_{a',b'}Φ_n(a',b')e^{-c_λ(|a'-a|+|b'-b|)}+Ψ_ne^{-c_λ|a-b|}+W^{-D}` for all `x∈[a]`, `y∈[b]` (pairs `x≠y` as in `BAGijGEX`). `Ω={‖G_t-M‖_max≤W^{-ε₀}}` (`FlowFM.indMax`, `Step1Boot.lean:54`; the event form of §72 (5) / D539). The premise carries `1_Ω`, a weaker hypothesis than `(eq:def_Psit)` (`7_8:1924`): in that respect the pin is stronger than the printed lemma.
- `BAGbEXPii'`: not needed. G.3 proves the existing `BAGbEXPii` (`Step1Boot.lean:108`) from the same argument, and it is what the consumers use (`baGii_member`, `flowFM_wl_det` hypothesis `hii`). The printed `(GiiGEX_BA)(a)` follows with `max𝓛≺Ψ²`. Decision requested: `BAGbEXPii':=BAGbEXPii`, no new pin.
- `BAGbEXPav'`: unchanged form (`BAGavLGEX`, `Step1Boot.lean:97`, the deterministic `Ψ`, window and `STInitialGT2gL` are the paper's); `Φ` plays no role in the averaged law.
- Consumers: `baBootstrap'_holds` (`Step1.lean:576`) and `baStep1_holds` (`Step1Fam.lean:695`) take `BAGbEXPij'` in place of `BAGbEXPij`; `baGij_member` supplies `Φ_n≡(Nτ g)^{1/2}`, `Ψ_n²=Nτ g≥W^{-d}` from the premise `omegaC·‖𝓛‖≤Nτ g` (event bookkeeping: G7); in `flowFM_wl_det` (`Step1Setup.lean:113`) the hypothesis `hij` (window `gexRHS`, `:69`) is replaced by the primed bound and the constant `2·9^d+1=1459` (`:125`, docstring `:112`) by `3S⁴+4`, `S=expC(d-2,c_λ)` (from `|Δ|²≤3(φ²S⁴+Ψ²+W^{-2D})`). Row G7 (C3).

### G.8 (vii) Split, files, size (lo / central / hi lines; stop line 2000 binding for G3a)
| row | file | Lean statements (pins of the intermediate lemmas; mathematics above) | lo / central / hi |
|---|---|---|---|
| G3a (this ticket, 1b) | `BA/GreenCore.lean` (ns `RBM.BA`, stem `GreenCore_`) | R1 identities (E0)-(E3), (E1'): 180; R2 LDE error bounds on `𝔛,Q^{XX},Q^{XD},ε,X_uu` from the four `BALDEin` Props: 300; R3 two-sided inequality `R_{a,y}`: 350; R4 coupled bound `‖Δ‖≤K_BA‖𝒦‖` (hypotheses: `BAStab K_Θ`, `ρ`, `ρ₂≤1`) and the diagonal law: 270; R5 the pin `BAGbEXPij'`, the Prop `BAStab` (shape of `Stable`), registry `owedProps` lines, instances: 200 | 800 / 1300 / 1950 |
| G3b | `BA/GreenStab.lean` | `BAStab` at `BAReal` data with `K_Θ=16κ⁻⁴` (S1); `ρ`, `ρ₂` at `BAReal` data (S3); public translation invariance and `ℓ¹` row of `Θ` (S2); instance | 300 / 450 / 741 (design 300 / 484 / 741) |
| G4 | `BA/GreenOff.lean` | weighted closure (G.4), the deterministic core of `BAGbEXPij'` with `c_λ`, `Ψ`-term; consumed by G6a/G6b | 500 / 800 / 1200 (design) |
Dependencies: G3b needs only merged files (not G3a, not T2389): it can run at the C2 REQ, before G3a's 1b; G4 needs G3a and G3b; G3a's 1b needs T2389 (`BALDEin`). G3a's instance keeps `BAStab` (G3b's pin) and `BALDEin` as hypotheses (other gates' pins); the event hypothesis with the analytic `K_BA` (`δ≈10^{-21}`) is met at `t=0` (`X=0`, `Δ=0`); for `t>0` no concrete sample reaches that `δ` (R2).

### G.9 Open issues, risks, paper-delta candidates
- R1 (blocks the 1a-audit criterion "primed pins compile in the probe"): not done in this run, the role bars Lean. The pins are specified in G.7; the compile in `RBM3D/Probe/T2390Pins.lean` must be done by the hub or at the start of 1b. `BAGbEXPij'`, `GreenCore` are absent on `main` (grep: no match in `RBM3D/`).
- R2: the analytic `K_BA` (1e18-1e28) makes every closure `K_BAδ≤1/2` an eventual statement; instances need the event at `t=0` or an event hypothesis. The observed `K_BA` (1.6, 31, 1355) is not provable at concrete data in Lean by a short term.
- R3: G.3 two-sided inequality, G.4 weights and the in-block fluctuation-averaging reading are arguments, checked only through the identities (E0)-(E3) and the stability bound (`chk.out`), not at small `δ` (the finite-size sample has `δ=0.32`).
- R4: `κ(g=𝔡⁻¹)` is `L`-dependent (G.5); the BA main theorem needs the bulk `κ`, so constants at `g=𝔡⁻¹` are those at `κ≈0.04`.
- Paper-delta candidates: `T2390a` the primed `BAGbEXPij'` has the paper's `(GijGEX_BA)` shape with the event `1_Ω` on premise and conclusion (formalization requirement, D539) and without the premise `max𝓛≺Ψ²` (the proof needs only `Ψ_t≥W^{-d/2}`); `T2390b` the stability constant of the BA diagonal equation is `16κ⁻⁴` from `BAoffDiag_scalar` (not from `prop:ThfadC_short`); `T2390c` note on `T2378` §5: `κ` at `g=𝔡⁻¹` is 0.044 at large `L`, not 0.262.

## Verdicts
- G3a: PASS (stage-1b scope fixed in G.8; argument closes with C1-permitted facts only).
- G3b: PASS (`BAStab` from `BAoffDiag_scalar`; independent of G3a).
- G4: PASS (design closes; weights and `c_λ` fixed in G.4; depends on G3a, G3b).
- Condition for the 1a-audit: R1 (compile of the primed pins) is open.

## (a″) Probe compile (Amend 1 D1) — Sat Oct 10 21:40:30 UTC 2026

Step role `prover-max`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2390`, branch `t/T2390`, commit `10fcef2` (one file `RBM3D/Probe/T2390Pins.lean`, never merged, no root import). Sections (a) and (G) are not edited. R1 of G.9 (compile of the primed pins in the probe) is done by this step.

Compile, run at `date -u` = Sat Oct 10 21:39:20 UTC 2026 (command, verbatim output, exit code):
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2390 && lake env lean RBM3D/Probe/T2390Pins.lean
BAStab : ℕ → (L : ℕ) → [NeZero L] → ℝ → ℝ → ℂ → ℝ → ℝ → Prop
@GreenCore_loopPrem : {d : ℕ} →
  (sz : Sizes d) → (ℕ → ℂ) → (ℕ → ℝ) → ℝ → ((n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → ℝ) → Prop
GreenCore_decayRHS : (d L : ℕ) → ℕ → [NeZero L] → ℝ → ℝ → (Zd d L → Zd d L → ℝ) → ℝ → Zd d L → Zd d L → ℝ
@GreenCore_decayConcl : {d : ℕ} →
  (sz : Sizes d) → (ℕ → ℂ) → (ℕ → ℝ) → ℝ → ℝ → ℝ → ((n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → ℝ) → (ℕ → ℝ) → Prop
BAGbEXPij' : ℕ → Prop
BAGbEXPii : ℕ → Prop
BAGbEXPav : ℕ → Prop
BAGbEXPij : ℕ → Prop
baBootstrap'_holds : ∀ (d : ℕ), BAFlowMember d → BAGbEXPii d → BAGbEXPij d → BABootstrap' d
baStep1_holds : ∀ (d : ℕ), BAGbEXPii d → BAGbEXPij d → BAStep1 d
SizesInst.sz0_values : SizesInst.sz0.L 0 = 4 ∧
  SizesInst.sz0.W 0 = 32 ∧ SizesInst.sz0.size 0 = 2097152 ∧ SizesInst.sz0.lam 0 = 1 / 64
EXIT=0
```
Scope and hygiene (script):
```
$ lake build --no-build RBM3D.BA.Step1Boot RBM3D.BA.GreenLDE RBM3D.BA.Prop5Short RBM3D.BA.Step1 RBM3D.BA.Step1Fam | tail -1
All targets up-to-date (3776 jobs).
$ grep -nE 'sorry|admit|axiom|native_decide' RBM3D/Probe/T2390Pins.lean; echo grep-exit=$?
grep-exit=1
$ git -C /Users/junyin/Lean_proof/RBM3D --no-optional-locks diff --stat main...t/T2390
 RBM3D/Probe/T2390Pins.lean | 176 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 176 insertions(+)
$ git -C /Users/junyin/Lean_proof/RBM3D --no-optional-locks grep -n -e BAStab -e GreenCore_ -e "BAGbEXPij'" main -- RBM3D | wc -l
       0
$ git -C /Users/junyin/Lean_proof/RBM3D --no-optional-locks rev-parse --short main
e207344
```
Statements, extracted by script (`sed -n '44,47p;54,59p;64,67p;71,77p;85,96p' RBM3D/Probe/T2390Pins.lean`; `BAStab` 44-47, `GreenCore_loopPrem` 54-59, `GreenCore_decayRHS` 64-67, `GreenCore_decayConcl` 71-77, `BAGbEXPij'` 85-96):
```
def BAStab (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (t K : ℝ) : Prop :=
  ∀ (v : Zd d L → ℂ) (B : ℝ),
    (∀ a, ‖v a - (t : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * v b‖ ≤ B) →
      ∀ a, ‖v a‖ ≤ K * B
def GreenCore_loopPrem {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ : ℝ)
    (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z).L n (t n) ![false, true] ![p.1, p.2] ω‖)
    (fun n p _ => Φ n p.1 p.2 ^ 2)
def GreenCore_decayRHS (d L W : ℕ) [NeZero L] (c D : ℝ) (Φ : Zd d L → Zd d L → ℝ) (Ψ : ℝ) (a b : Zd d L) : ℝ :=
  (∑ a' : Zd d L, ∑ b' : Zd d L, Φ a' b' *
      Real.exp (-c * ((zdistInf d L (a' - a) : ℝ) + (zdistInf d L (b' - b) : ℝ)))) +
    Ψ * Real.exp (-c * (zdistInf d L (a - b) : ℝ)) + (W : ℝ) ^ (-D)
def GreenCore_decayConcl {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ D c : ℝ)
    (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0))
    (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
    (fun n p ω => (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z).GM n (t n) ω p.1.1 p.1.2‖)
    (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (STblk sz n p.1.1) (STblk sz n p.1.2))
def BAGbEXPij' (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ c : ℝ, 0 < c ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
          ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
            ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
              (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
              (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
              (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
              GreenCore_loopPrem sz z t ε₀ Φ →
              GreenCore_decayConcl sz z t ε₀ D c Φ Ψ
```
Nonemptiness `example`s of the same file, compiled in the run above:
- line 120: `BAReal 3 4 0 (1 / 2) 0 Complex.I ∧ BAStab 3 4 0 0 Complex.I (1 / 2) 1` (zero coupling: `M^{(B)} = i·1`, `M^{(+,+)} = -1`, `t = 1/2`, `K = 1`).
- line 149: a `BAReal` datum `(g, E, m)` with `g = BAflowLam0 sz0 zSeq 0 > 0` at `L = sz0.L 0 = 4` (`SizesInst.sz0_values`, the last `#check` result; from `flow_sz0`, `BAflow_real`): the data of `BAStab` at positive coupling is nonempty.
- line 160: `BAGbEXPij' 3` applied at `SizesInst.sz0`, `FlowPinsInst.flow_sz0` (`κ = 1/2, ε = 1/10, 𝔠 = 1/6, 𝔡 = 1/10`), `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`), `ε₀ = 1/10`, `Φ ≡ W^{-1/10}`, `Ψ = W^{-1}`. `BAFlow`, `0 ≤ t ≤ T₀`, `ε₀ > 0`, `D > 0` and the three windows are discharged. The pin `h : BAGbEXPij' 3` (owed) and the loop premise `GreenCore_loopPrem` (`(eq:def_Psit)`) remain hypotheses.

Notes (each checkable in the file):
- `BAGbEXPij'` reads G.7 in the order `∀ κ ε 𝔡` (line 86), `∃ c > 0` (87), `∀ 𝔠 sz z` with `BAFlow` (88), `∀ t` with `0 ≤ t n ≤ BAflowT0 sz z n`, `∀ ε₀ > 0`, `∀ D > 0`, `∀ Φ Ψ`, the three windows as `∀ᶠ n` (92-94, as in `BAGavLGEX`, `Step1Boot.lean:97-103`), the loop premise (95), the decay conclusion (96).
- Premise and conclusion carry `Ω = {‖G_t - M‖_max ≤ W^{-ε₀}}` through `FlowFM.indMax` (lines 57, 75), the carrier `baFMz sz z` and the law `seqP (sz.withLam 0)` of `BAGijGEX` (`Step1Boot.lean:88-93`); pairs `x ≠ y` as `BAGijGEX` (line 74); distances are `zdistInf` (lines 66-67, as in `FlowFM.gexRHS`).
- `BAStab` is `Stable S ξ K` (`Green/EntryCore.lean:911`) with the complex kernel `BAMss … true true` and `ξ = t`, data-explicit in `(d, L, g, E, m, t, K)` so that R4 can read it at the flow data `(BAflowLam0, BAflowEs, BAmF)`. Its bound `K = 16κ⁻⁴` at `BAReal` data is (S1), G3b's theorem: neither stated nor proved here.
- Not in the probe: `BAGbEXPii'` (Amend 1 D2: the merged `BAGbEXPii` stands in; `#check` above) and `BAGbEXPav'` (unchanged). The merged consumers `baBootstrap'_holds`, `baStep1_holds` take `BAGbEXPii d → BAGbEXPij d` (their two `#check` results in the output above); their primed successors (G.7, row G7) are not written.
- The probe checks well-formedness and nonemptiness of the hypotheses. It does not test the truth of `BAGbEXPij'`, or of `BAStab` at positive coupling.

Paper-delta candidates (proposed; the dispatcher numbers them): `T2390e`: the pin is for pairs `x ≠ y` (line 74), printed (b) `7_8:1940-1944` has `max_{x∈[a], y∈[b]}`, including `x = y`. `T2390f`: `c` is fixed after `(κ, ε, 𝔡)` and before `(𝔠, sz, z, t, ε₀, D, Φ, Ψ)` (lines 86-88); printed: "There exists a constant `c_λ`" (`7_8:1941`), no order stated.

## (a′) Preflight corrections (Amend 1 D3, D4) — Sat Oct 10 21:51:03 UTC 2026
Replaces: G.3 "two-sided inequality" and its closure `ρδ≤1/4` (non-local `sup R`); G.4 linear part and "`|𝒦₀(a',b')|≲Φ+W^{-d/2}|M|`"; the last sentence of G.8 (`t=0` instance). G.7 per D2: `BAGbEXPii` stands in (T2390d); pins as compiled in (a″). Mathematics only; every constant below is derived in the lines shown. Not machine-checked: (R*), (X*), (C1), (C2) are proofs on paper (the identities they use are the checked (E0)-(E3), (E1′), `chk.out`).
**Notation.** `|·|=zdistD` (`zdistInf≤zdistD`, so decay in `|·|` implies the printed `zdistInf` form); `c₀=BAct_rate`, `μ=BAp5s_rate`, `S_γ=expC(d−2,γ)≥Σ_z e^{-γ|z|}` (`BAsum_exp_decay_le`, `Prop5Short.lean:251`); `ν=c₀/2`, `ρ̂=c₀⁻¹S_{c₀/2}≥Σ_b|M_ab|e^{ν|a−b|}`, `ρ=sup_cΣ_b|M^{(B)}_{bc}|`; `Φ_N=N^τ≥1` with `τ<𝔠ε₀` (`W≥N^𝔠`), `δ=W^{-ε₀}`, `a=Φ_N^{1/2}δ`; the pin's window `W^{-d/2}≤Ψ≤W^{-ε₀}` forces `ε₀≤d/2`, so `W^{-d}≤δ²`. All bounds hold on `Ω={‖Δ‖≤δ}` and the LDE events (`baLDEin_holds`, `GreenLDE.lean:199`, merged T2389), uniformly over the `≤N²` index pairs.
**D3.1 Crude bounds (Ω and Kronecker support only).** `M_vw=0` for `v≠w` in one block (offsets differ), likewise `M_lk=0` for `l∈N(w)`, `k∈[w]\w`; so those `G`-entries are `Δ`-entries, `≤δ`. `M_uu=m`, `|m|≥κ`, so `|G_uu|≥κ−δ≥κ/2` (`δ≤κ/2`). Minor identity: `G^{(w)}_{vy}=G_vy−G_vwG_wy/G_ww`, hence
`(m1)  |G^{(w)}_{vy}|² ≤ 2|G_vy|²+(8/κ²)|G_vw|²|G_wy|²`.
With `R_{a,y}:=W^{-d}Σ_{v∈a}|G_vy|²`, `R̃_u:=W^{-d}Σ_{v∈[u]\u}|G_vu|²≤δ²`, LDE of `X_{u·}` against `G^{(u)}_{·y}` and (m1) give `(L1) |𝔛_uy|²≤Φ_N[2R_{[u],y}+(8/κ²)R̃_u|G_uy|²]`. For `𝒜_w:=tm+X_ww−Q^{XX}_w−Q^{XD}_w=−tv̄_{[w]}+ε_w+X_ww−Q^{XD}_w` (E2; the column twin of (E1′) has the same form with `𝔛'`): `t|v̄|≤δ`; `|X_ww|≤a`; `|ε_w|≤5a` (`W^{-2d}Σ_{v,k∈[w]\w}|G^{(w)}_{vk}|²≤8δ²` since `|G^{(w)}_{vv}|≤2`, `|G^{(w)}_{vk}|≤2δ`; `tW^{-d}|G_ww+Σ_kG_kwG_wk/G_ww|≤2δ`); `|Q^{XD}_w|≤2dg₀(2+32κ⁻²)^{1/2}a` from (L1) with `R_{[w],l}≤δ²`, `|G_wl|≤2`. So `(A*) |𝒜_w|≤C_𝒜a`, `C_𝒜=7+2dg₀(2+32κ⁻²)^{1/2}`.
**D3.2 Two-sided inequality for `R_{a,y}`, `y=(c,o)`.** (E0) `Δ=−GYM` and (E1′): `Δ_xy=−Σ_{b'}M^{(B)}_{b'c}[𝒜_wG_xw+𝔛'_xw]`, `w=(b',o)` (`M_wy=1_{o(w)=o(y)}M^{(B)}_{b'c}`). Cauchy–Schwarz with weights `|M_{b'c}|`, `|Z|²≤2|𝒜|²|G|²+2|𝔛'|²`, average over `x∈a`, LDE in the column of `w` and (m1) (`W^{-d}Σ_{k∈b'\w}|G_wk|²≤δ²`; `W^{-2d}Σ_{x∈a,k∈b'}|G_xk|²=𝓛^{(2)}_{(a,b')}`) give
`(R1)  R_{a,(c,o)} ≤ 2W^{-d}|M_{ac}|² + 8ρΦ_NΣ_{b'}|M_{b'c}|𝓛^{(2)}_{(a,b')} + 4ρΣ_{b'}|M_{b'c}|·ϑ·R_{a,(b',o)}`, `ϑ=(𝒜*)²+8Φ_Nδ²/κ²≤C_ϑa²`, `C_ϑ=C_𝒜²+8κ⁻²`.
Terms: (T_a) `avg_x|M_xy|²`: exactly one `x∈a` has the offset of `y` (the `W^{-d}`); (T_b) the `𝔛'` part: LDE + (m1) + `x`-average = a loop (`avg_x|𝔛'_xw|²≤Φ_N[2𝓛_{(a,b')}+(8/κ²)δ²R_{a,w}]`); (T_c) the `𝒜_wG_xw` part. Left side `R`, right side `𝓛` (note `𝓛^{(2)}_{(a,c)}=W^{-d}Σ_{y∈c}R_{a,y}` is the average of the left side).
**Local closure (no `sup R`).** For fixed `(a,o)`, `r_c:=R_{a,(c,o)}` satisfies `r≤f+Pr`, `P_{cb'}=4ρϑ|M_{b'c}|`, `f_c=(T_a)+(T_b)`. The absorbed term is `4ρϑΣ_{b'}|M_{b'c}|r_{b'}`, a local operator. `(C1) 8ρρ̂ϑ≤1` gives `Σ_{b'}P_{cb'}e^{ν|c−b'|}≤½`, so (finite `L`: `r≤Σ_{k<n}P^kf+P^nr`, `‖P‖≤½`) `(Σ_kP^k)_{cb'}≤2e^{-ν|c−b'|}`. With `|M_{ac}|≤c₀⁻¹e^{-c₀|a−c|}`, `ν=c₀/2` (`ν|c−c'|+2c₀|a−c'|≥ν|a−c|+3ν|a−c'|`; `ν|c−c'|+c₀|b'−c'|≥ν|c−b'|+ν|b'−c'|`):
`(R*)  R_{a,(c,o)} ≤ C_R[W^{-d}e^{-ν|a−c|}+Φ_NΣ_{b'}Φ(a,b')²e^{-ν|c−b'|}]`, `C_R=max(4c₀⁻²S_{3ν},16ρ̂c₀⁻¹S_ν)`, using the premise `𝓛^{(2)}≺Φ²`. Condition (C1) holds for `Φ_Nδ²≤1/(8ρρ̂C_ϑ)`: eventual in `n`, depends on `(d,κ,𝔡)` only.
**D3.3 Local bounds on `𝔛` and `𝒜'`** (replace "`𝒦₀≲Φ+W^{-d/2}|M|`"). (L1)+(R*) (with `R̃_u≤R_{a,a}` and `R̃_u^{1/2}|M_{ac}|`: `e^{-ν|a−b'|/2−c₀|a−c|}≤e^{-ν|c−b'|/2}`): for `u=(a,·)≠y=(c,·)`
`(X*)  |𝔛_uy| ≤ C_XΦ_N[W^{-d/2}e^{-(ν/2)|a−c|}+Σ_{b'}Φ(a,b')e^{-(ν/2)|c−b'|}] + (3/κ)a|Δ_uy|`, `C_X=√(2C_R)(1+2/(κc₀))`.
`(Ξ) |𝒜'_w|:=|ε_w+X_ww−Q^{XD}_w| ≤ C_ΞΦ_N[W^{-d/2}+Σ_{b''}Φ(b',b'')e^{-(ν/2)|b'−b''|}] + (3dg₀/κ)aΣ_{l∈N(w)}|Δ_wl|`, `C_Ξ=6+5κ⁻¹√C_R+2dΛe^{ν/2}C_X` (`Q^{XD}` piece: (X*) at `y=l`, `|[l]−b'|=1`; `ε`: `𝓛_{(b',b')}≤Φ(b',b')²`, `R̃≤R_{b',b'}`, (R*)).
**D3.4 G.4 linear part restated.** Expanding (E3) with `𝒜=−tv̄+𝒜'`, `G=M+Δ`: `Δ_xy=L1+L2+L3+Q`, `L1=−Σ_{b'}M_{ab'}𝒜'_wM_wy`, `L2=−Σ_{b'}M_{ab'}𝔛_wy1_{w≠y}`, `L3=tΣ_{b'}M_{ab'}v̄_{b'}M_{b'c}1_{o(x)=o(y)}`, `Q=Σ_{b'}M_{ab'}(tv̄_{b'}−𝒜'_w)Δ_wy`. Block-averaging the diagonal: `v̄=Θ_tu`, `u_a=avg_{k∈a}(L1+L2+Q)_{kk}`, `Θ_t=(1−tM^{(+,+)})⁻¹`, `|Θ_{ba}|≤C₅(1_{a=b}+g₀²e^{-μ|a−b|})` (`baProp5s_holds`, `Prop5Short.lean:667`; translation invariance: G3b publishes it).
Target kernel `𝔗_c(a,c')=Σ_{a',b'}Φ(a',b')e^{-c(|a'−a|+|b'−c'|)}+Ψe^{-c|a−c'|}`: `𝔗_c(a'',c'')≤e^{c(|a−a''|+|c'−c''|)}𝔗_c(a,c')`, so for `c≤c₀/2` `Σ_{b'}|M_{ab'}|𝔗_c(b',c')≤ρ̂𝔗_c(a,c')` (rate preserved). Linear sources: `L1`: `|b''−c|≤|b''−b'|+|b'−c|`, `Ψ≥W^{-d/2}`; `L2`: (X*) with `e^{-c₀|a−b'|}`; both `≤C_ℓΦ_N𝔗_{c₀/4}(a,c)`, and `|u^{lin}_a|≤C_ℓΦ_N𝔗_{c₀/4}(a,a)`; `L3^{lin}`: with `|a''−a|+|b''−c|≤(|a''−a'|+|b''−a'|)+2|a'−b'|+|a−b'|+|b'−c|`, the exponent of `e^{-c₀(|a−b'|+|b'−c|)−μ|b'−a'|−(c₀/4)(|a''−a'|+|b''−a'|)}` dominates `3c_λ(|a''−a|+|b''−c|)` for
`c_λ = min(c₀, μ/2, c₀/4)/3 = min(c₀/12, μ/6)` (`μ≤c₀`; `c_λ≤c₀/2`; leftover rates `≥2c_λ` make the sums finite). Absorbed (Δ-linear) terms: `Q`, the `Δ` parts of (X*), (Ξ), and the `Θ`-feedback `u^Q`: with `η=C_ηa`, `C_η=C_𝒜+(3/κ)(1+2dΛe^{c_λ}ρ̂/c₀)`, `C_Θ̂=C₅(1+Λ²S_{2μ/3})≥sup_bΣ_{a'}|Θ_{ba'}|e^{2c_λ|b−a'|}`: `(C2) η(ρ̂+ρ̂²c₀⁻¹C_Θ̂)≤½`. `𝒩:=max_{a,c}max_{x∈a,y∈c}|Δ_xy|/𝔗_{c_λ}(a,c)` is finite (`Φ>0`) and `𝒩≤C_ℓ'Φ_N+½𝒩`, so `|Δ_xy|≤2C_ℓ'Φ_N𝔗_{c_λ}(a,c)` for all `x,y` (the diagonal `x=y` included, it feeds `v̄`). The paper's `W^{-D}` term is not needed; no iteration to `W^{-D}`. No `g≤W^{-ε}`, no `(Cλ)^{|a−b|}`, no smallness of `‖M−m₀I‖` (C1): `g₀≤Λ` enters through `ρ̂`, `C_𝒜`, `C₅`. Row map: R3 of G3a = `(m1)`, (R1), (R*), (X*), (Ξ); G3b = `Θ` weights `C_Θ̂`, `BAStab`; G4 = D3.4 closure; the old claim "G.3 then gives `𝒦₀`" is withdrawn.
**D4 Instance plan for G3a's endpoints (replaces `t=0`).** Data: `d=3`, `L=4`, `t=1/2>0` (`half_lt_t0`, `FlowPins.lean:1254`), the flow datum `(g₀,E,m₀)` (`BAReal`, `κ` as in the table), `W,Φ_N,δ` real parameters with `W^{-d}≤δ²`, `δ≤κ/2`. R1 (identities): explicit in-block Hermitian `X≠0`, `Y=X+tm`, `G=(H−z)⁻¹` (`Im z>0`), so `Δ=−MYG≠0`. R3/R4: `Δ:=δ·E` with `E_xy=1_{x=y}+½·1_{x≠y,o(x)=o(y)}` (`‖Δ‖_max=δ≠0`), `𝒦:=M⁻¹Δ−𝒮[Δ]M` (so (E3) holds). Numbers: `ρ=L^d=64` (same-offset sites × `‖M_xy‖≤1`, `BAMfine_norm_le_one`, `GreenSchur.lean:105`), `ρ̂=64e^{6ν}` (`ℓ¹` diameter 6), `ρ₂≤1`, `K_Θ=16κ⁻⁴`, `K_BA=ρ(1+ρ₂K_Θ)`. Other gates' pins that stay hypotheses: `BAStab K_Θ` (G3b); the pin `BAGbEXPij'` and `GreenCore_loopPrem` (R5 example = probe line 160). `BALDEin` is discharged: `baLDEin_holds 3` (`GreenLDE.lean:199`, merged b6cc9d2), not a hypothesis. Closure at `sz0` (`W=32`) is impossible with the provable `ρ=64` (`δ≥W^{-3/2}`); the R3/R4 instance uses larger `W` (the Lean `W` there is a number, the datum is the `BAReal` one). Command (`inst.py`, `sz0.py`; `g₀` = row `g₀=√t₀g` of table (i)) and output:
```
$ python3 inst.py        (columns: g kappa g0 c0 mu c_lam rho_hat K_Th K_BA C_A C_th W eps0 delta window N^(1/6)<=W Adm delta<=k/2 W^-d<=d^2 (C1) K_BA*delta<=1/2)
0.01562 0.5   0.013  4.16e-03 1.29e-32 2.14e-33  64.80  256   16448   7.9   9.42e+01  4096  1.4  8.76e-06  [3.81e-06,8.76e-06] True  128<=4096 True  True  True  True  7.20e-04 True  0.144 True
1      0.25  0.561  2.08e-03 9.89e-38 1.65e-38  64.40  4096  262208  83.3  7.07e+03  16384 1.4  1.26e-06  [4.77e-07,1.26e-06] True  256<=16384 True  True  True  True  1.11e-03 True  0.330 True
10     0.25  4.6723 2.08e-03 9.89e-38 1.65e-38  64.40  4096  262208  642.6 4.13e+05  16384 1.4  1.26e-06  [4.77e-07,1.26e-06] True  256<=16384 True  True  True  True  6.47e-02 True  0.330 True
$ python3 sz0.py
sz0 W=32 g=0.01562: (C1) 8*64*rho_hat*C_th*Phi*delta^2 at delta=W^-3/2 = 286 <= 1: False
sz0 W=32 g=1: (C1) 8*64*rho_hat*C_th*Phi*delta^2 at delta=W^-3/2 = 2.13e+04 <= 1: False
sz0 W=32 g=10: (C1) 8*64*rho_hat*C_th*Phi*delta^2 at delta=W^-3/2 = 1.25e+06 <= 1: False
```
(`Φ_N=3`, `Λ=10`, `ε₀=1.4<d/2`; window `[W^{-3/2},W^{-ε₀}]` nonempty, `Kδ≤½`, (C1) hold at all three `g`; `c_λ` is `2.1e-33 / 1.7e-38 / 1.7e-38`: positive, `(d,κ,𝔡)` only, existence only as in table (i).)
**Verdicts after (a′).** D3 closed: the `R` closure is local (kernel `e^{-ν|c−b'|}`) and G4's closure is in the ratio norm `𝒩` (weights tracked, `c_λ=min(c₀/12,μ/6)`). G3a PASS, G3b PASS, G4 PASS. Paper-delta candidates added: `T2390g` (decay rate `c_λ=min(BAct_rate/12, BAp5s_rate/6)`, so it depends on `μ` as well as `c₀`; the `W^{-D}` term of `(GijGEX_BA)` is not used by this proof); `T2390d` per Amend 1 item 1.

## (b) Stage 1b, escalation round: script output — Sun Oct 11 00:40:50 UTC 2026 (claude-opus-5-5; branch `t/T2390` at `e34b6d6`)

This section and (c), (d) replace those of the prover-max round (header `Sat Oct 10 23:59:52 UTC 2026`, claude-sonnet-5-5, branch at `6fcdc83`); line 1 of this file read `Prover model: claude-sonnet-5-5` before this round. Sections (a), (a″), (a′) are unchanged; no (a′) correction was needed.

**Stability constants first** (ticket report rule): `K_Θ = 16κ⁻⁴` of `BAStab` ((a) G.2 (S1), owner G3b), `κ` from (a) (i)/(ii).
```
$ python3 -c "[print(n,k,16/k**4) for n,k in (('g=1/64 (L=4)',.5),('g=1 (L=4)',.25),('g=10 (L=4)',.25),('g=10 (L->inf)',.04))]"
g=1/64 (L=4) 0.5 256.0
g=1 (L=4) 0.25 4096.0
g=10 (L=4) 0.25 4096.0
g=10 (L->inf) 0.04 6250000.0
```
**Size (stop line 2000), build, hygiene.**
```
$ wc -l RBM3D/BA/GreenCore.lean
    1981 RBM3D/BA/GreenCore.lean
$ for h in 29f2219 5b2b129 c94ffbe 6b01f58 8956602 6fcdc83 e34b6d6; do echo $h $(git show $h:RBM3D/BA/GreenCore.lean | wc -l); done | paste -sd'|' -
29f2219 1265|5b2b129 1576|c94ffbe 1665|6b01f58 1971|8956602 1971|6fcdc83 1975|e34b6d6 1981
$ lake build RBM3D.BA.GreenCore 2>&1 | tail -3   # finished before `date -u` = Sun Oct 11 00:32:16 UTC 2026; file content = commit e34b6d6
Note: This linter can be disabled with `set_option linter.style.longLine false`
✔ [3777/3777] Built RBM3D.BA.GreenCore (37s)
Build completed successfully (3777 jobs).
$ grep -nE 'sorry|admit|axiom|native_decide' RBM3D/BA/GreenCore.lean; echo grep-exit=$?
grep-exit=1
$ lake env lean docs/tickets/checks/T2390-check.lean > check.out 2>&1; echo "check file exit=$?"; grep -c error check.out
check file exit=0
0
$ printf 'import RBM3D\nimport RBM3D.BA.GreenCore\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean > pre.out 2>&1; echo "registry pre-check exit=$?"; grep -E "BAStab:|BAGbEXPij':|unregistered|error" pre.out
registry pre-check exit=0
  RBM.BA.BAStab: 1 [no certificate]
  RBM.BA.BAGbEXPij': 0 [no certificate]
$ grep -n "premises found by scanning" pre.out
102:premises found by scanning: 124 (borrowed 1, owed 58, structural 46, refuted 6, superseded 13).
$ # temporary, not committed: `import RBM3D.BA.GreenCore` after the last import of RBM3D.lean; RBM3D.lean restored from a copy afterwards
$ (time lake build) > fullbuild.out 2>&1; echo exit=$?; grep -E "axiom audit|Build completed|error" fullbuild.out | head
exit=0
info: RBM3D.lean:437:0: axiom audit: 11275 theorems, 3383 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4205 jobs).
```
**Statements of the previous round unchanged** (its proofs were shortened to fit the stop line):
```
$ diff chk_before.out chk_after.out && echo "81 #check outputs identical"   # `#check @RBM.BA.<n>`, the 81 public names of 6fcdc83, run at 6fcdc83 and at e34b6d6
81 #check outputs identical
$ python3 sigs.py   # every declaration of 6fcdc83 vs e34b6d6: signature text up to `:=`, whitespace-collapsed
declarations before: 125 after: 132 removed: [] added: ['GreenCore_Qxd_eq', 'GreenCore_T', 'GreenCore_T_nonneg', 'GreenCore_Rsq', 'GreenCore_Tshift', 'GreenCore_Xstar', 'GreenCore_Xi'] statement text changed: []
```
**Axioms** (`#print axioms RBM.BA.<n>` for the 88 public declarations, names generated from the file; selected lines):
```
$ grep -c "" ax.out; grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" ax.out
88
88
$ grep -E "'RBM.BA.(BAStab|BAGbEXPij'|GreenCore_(Xstar|Xi|Rbound|diag|coupled|T|Rsq|Tshift|Qxd_eq|T_nonneg))'" ax.out
'RBM.BA.GreenCore_Qxd_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_Rbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_T_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_Rsq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_Tshift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_Xstar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_Xi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAStab' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_coupled' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCore_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAGbEXPij'' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**Target statements** (`targets.py`: `file:line name hyps[...] ⊢ conclusion`, from the file text; full signatures in the file). Rows: R1 `E1`-`E3`; R2 `m1`-`Xcol_avg`; R3 `twoSided`, `Rstar`, `Rbound`, `Xstar` (X*), `Xi` (Ξ); R4 `coupled`, `diag`; R5 `carrier` and the pins below.
```
GreenCore.lean:84 GreenCore_E1 hyps[hGM hGuu] ⊢ ∑ v, X u v * G v y = (X u u - ∑ k ∈ univ.erase u, ∑ l ∈ univ.erase u, X u k * greenMinor G u k l * H l u) * G u y + ∑ v ∈ univ.erase u, X u v * greenMinor G u v y
GreenCore.lean:115 GreenCore_E1' hyps[hMG hGww] ⊢ ∑ k, G v k * X k w = G v w * (X w w - ∑ l ∈ univ.erase w, ∑ k ∈ univ.erase w, H w l * greenMinor G w l k * X k w) + ∑ k ∈ univ.erase w, greenMinor G w v k * X k w
GreenCore.lean:755 GreenCore_E0 hyps[hGR hMR hz] ⊢ G - M = -(G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M)
GreenCore.lean:642 GreenCore_E2 hyps[hM hMd hw] ⊢ (t : ℂ) * m - GreenCore_Qxx G X w = -((t : ℂ) * GreenCore_vbar G M w.1) + GreenCore_eps2 G t w - GreenCore_eps1 G X t w
GreenCore.lean:780 GreenCore_Delta_col hyps[hGR hRG hMR hz hM hG0] ⊢ G x y - M x y = -∑ b', Mb b' y.1 * (GreenCore_Acol G X D t m (b', y.2) * G x (b', y.2) + GreenCore_Xcol G X x (b', y.2))
GreenCore.lean:1214 GreenCore_Delta_row hyps[hGR hRG hMR hz hM hG0] ⊢ G x y - M x y = -∑ b', Mb x.1 b' * (GreenCore_Arow G X D t m (b', x.2) * G (b', x.2) y + GreenCore_Xrow G X (b', x.2) y)
GreenCore.lean:1253 GreenCore_E3 hyps[hGR hRG hMR hz hM hG0] ⊢ G x y - M x y = ∑ b', Mb x.1 b' * ((t : ℂ) * GreenCore_vbar G M b' * M (b', x.2) y) + ∑ b', Mb x.1 b' * GreenCore_K G M X D t m (b', x.2) y
GreenCore.lean:400 GreenCore_m1 hyps[hκ hw] ⊢ ‖greenMinor G w v y‖ ^ 2 ≤ 2 * ‖G v y‖ ^ 2 + (8 / κ ^ 2) * (‖G v w‖ ^ 2 * ‖G w y‖ ^ 2)
GreenCore.lean:450 GreenCore_Xrow_sq hyps[hκ hΦ hGuu hLrow] ⊢ ‖GreenCore_Xrow G X u y‖ ^ 2 ≤ Φ * (2 * GreenCore_R G u.1 y + (8 / κ ^ 2) * ‖G u y‖ ^ 2 * GreenCore_R G u.1 u)
GreenCore.lean:468 GreenCore_Xcol_sq hyps[hκ hΦ hGuu hLcol] ⊢ ‖GreenCore_Xcol G X x w‖ ^ 2 ≤ Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1)
GreenCore.lean:563 GreenCore_eps1_loc hyps[hκ hΦ hGuu hLquad] ⊢ ‖GreenCore_eps1 G X t w‖ ^ 2 ≤ Φ * (2 * GreenCore_loop G w.1 w.1 + (8 / κ ^ 2) * GreenCore_R G w.1 w * GreenCore_Rrow G w w.1)
GreenCore.lean:584 GreenCore_eps2_loc hyps[ht0 ht1 hκ hGuu] ⊢ ‖GreenCore_eps2 G t w‖ ^ 2 ≤ (4 / κ ^ 2) * GreenCore_R G w.1 w * GreenCore_Rrow G w w.1
GreenCore.lean:702 GreenCore_Qxd_sq hyps[hg hL hD hXr] ⊢ ‖GreenCore_Qxd G X D u‖ ^ 2 ≤ (2 * d * g₀) ^ 2 * Q
GreenCore.lean:729 GreenCore_Arow_four hyps[hM hMd hw] ⊢ ‖GreenCore_Arow G X D t m w + (t : ℂ) * GreenCore_vbar G M w.1‖ ^ 2 ≤ 5 * (‖GreenCore_eps2 G t w‖ ^ 2 + ‖GreenCore_eps1 G X t w‖ ^ 2 + ‖X w w‖ ^ 2 + ‖GreenCore_Qxd G X D w‖ ^ 2)
GreenCore.lean:796 GreenCore_Acol_sq hyps[hL hg hκ hGR hRG hMR hMR' hz hM hMd hD hκm hMb1 hGuu hΩ] ⊢ ‖GreenCore_Acol G X D t m w‖ ^ 2 ≤ (4 / κ ^ 2) * (2 * d * g₀ + (1 + 2 * d * g₀) / κ) ^ 2 * δ ^ 2
GreenCore.lean:501 GreenCore_crude hyps[hM hMd hMb1 hκm hm1 hδ hΩ] ⊢ (∀ u, κ / 2 ≤ ‖G u u‖) ∧ (∀ u v, ‖G u v‖ ≤ 3 / 2) ∧ (∀ u v, u.2 ≠ v.2 → ‖G u v‖ ≤ δ)
GreenCore.lean:524 GreenCore_apriori hyps[hG32 hGoff hδ0 hwd] ⊢ (∀ a y, GreenCore_R G a y ≤ 13 / 4 * δ ^ 2) ∧ (∀ x b, GreenCore_Rrow G x b ≤ 13 / 4 * δ ^ 2)
GreenCore.lean:855 GreenCore_Xcol_avg hyps[hΦ hκ hX hRrow] ⊢ ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖GreenCore_Xcol G X (a, o) w‖ ^ 2 ≤ Φ * (2 * GreenCore_loop G a w.1 + (26 / κ ^ 2) * δ ^ 2 * GreenCore_R G a w)
GreenCore.lean:903 GreenCore_twoSided hyps[hρ0 hκ hΦ0 hα hM hρ hΔ hA hX hRrow] ⊢ GreenCore_R G a (c, o) ≤ 2 * ((W : ℝ) ^ d)⁻¹ * ‖Mb a c‖ ^ 2 + 8 * ρ * Φ * ∑ b', ‖Mb b' c‖ * GreenCore_loop G a b' + 4 * ρ * (α2 + 26 / κ ^ 2 * Φ * δ ^ 2) * ∑ b', ‖Mb b' c‖ * GreenCore_R G a (b', o)
GreenCore.lean:320 GreenCore_Rstar hyps[hd0 hnn hsymm htri hc₀ hκ hdiag hdec hρe hS hw hρ hΦ hϑ hC1 hr0 hrf] ⊢ r c ≤ 4 * c₀⁻¹ ^ 2 * S * w₀ * Real.exp (-(c₀ / 2) * dd a c) + 16 * ρ * Φ * c₀⁻¹ * S * ∑ b'', Real.exp (-(c₀ / 2) * dd c b'') * φ b'' ^ 2
GreenCore.lean:972 GreenCore_Rbound hyps[hL hGR hRG hMR hMR' hz hM hMd hD hκ hκm hm1 hMb1 hc₀ hdec hρ hS hg hΦ hδ hδ0 hwd hΩ hLcol hC1 φ hφ] ⊢ GreenCore_R G a (c, o) ≤ 4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c₀ / 2) * (zdistD d L (a - c) : ℝ)) + 16 * ρ * Φ * c₀⁻¹ * S * ∑ b'', Real.exp (-(c₀ / 2) * (zdistD d L (c - b'') : ℝ)) * φ a b'' ^ 2
GreenCore.lean:1066 GreenCore_Xstar hyps[hL hGR hRG hMR hMR' hz hM hMd hD hκ hκm hm1 hMb1 hc₀ hdec hρ hS hg hΦ hδ hδ0 hwd hΩ hLrow hLcol hC1 φ hφ0 hφ] ⊢ ‖GreenCore_Xrow G X u y‖ ≤ Real.sqrt (2 * Φ) * ((1 + 2 / (κ * c₀)) * GreenCore_T d L W c₀ ρ S Φ φ u.1 y.1 + Real.sqrt 13 / κ * δ * ‖G u y - M u y‖)
GreenCore.lean:1130 GreenCore_Xi hyps[hL hGR hRG hMR hMR' hz hM hMd hD hκ hκm hm1 hMb1 hc₀ hdec hρ hS hg ht0 ht1 hΦ hδ hδ0 hwd hΩ hLrow hLcol hLquad hLdiag hC1 φ hφ0 hφ] ⊢ ‖GreenCore_Arow G X D t m w + (t : ℂ) * GreenCore_vbar G M w.1‖ ≤ Real.sqrt 13 / κ * δ * (1 + Real.sqrt (2 * Φ)) * GreenCore_T d L W c₀ ρ S Φ φ w.1 w.1 + Real.sqrt (2 * Φ) * φ w.1 w.1 + Real.sqrt (Φ * ((W : ℝ) ^ d)⁻¹) + Real.sqrt (2 * Φ) * ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀) * GreenCore_T d L W c₀ ρ S Φ φ w.1 w.1 + Real.sqrt 13 / κ * δ * ∑ l, ‖D l w‖ * ‖G w l - M w l‖)
GreenCore.lean:1276 GreenCore_coupled hyps[hM ht0 ht1 hKθ hρ hρ₂ hv hE3 hstab hK] ⊢ ‖Δ x y‖ ≤ ρ * (1 + ρ₂ * Kθ) * K𝒦
GreenCore.lean:1361 GreenCore_diag hyps[hL hGR hRG hMR hMR' hz hM hMd hD hκ hκm hm1 hMb1 hc₀ hdec hρ hS hg ht0 ht1 hΦ hδ hδ0 hwd hΩ hLrow hLcol hLquad hLdiag hC1 hLm hLm0 hMb hstab hKθ hρr hρ₂ hKδ] ⊢ ‖G x y - M x y‖ ^ 2 ≤ 8 * (ρ * (1 + ρ₂ * Kθ)) ^ 2 * (9 / 4 * GreenCore_Ab d κ Φ δ c₀ ρ S g₀ ((W : ℝ) ^ d)⁻¹ Lm + GreenCore_Xb κ Φ c₀ ρ S ((W : ℝ) ^ d)⁻¹ Lm)
GreenCore.lean:1532 GreenCore_carrier hyps[hκ h ht0 ht hm hs hzt] ⊢ GreenCore_Gc sz z n t ω * (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω - zt • 1) = 1 ∧ (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω - zt • 1) * GreenCore_Gc sz z n t ω = 1 ∧ (GreenCore_Dc sz z n - s • 1) * GreenCore_Mc sz z n = 1 ∧ GreenCore_Mc sz z n * (GreenCore_Dc sz z n - s • 1) = 1 ∧ zt = s - (t : ℂ) * m ∧ (∀ u v, GreenCore_Mc sz z n u v = if u.2 = v.2 then BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) m u.1 v.1 else 0) ∧ (∀ a, BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) m a a = m) ∧ (∀ u l, GreenCore_Dc sz z n u l = if u.2 = l.2 ∧ Adj d (sz.L n) u.1 l.1 then ((BAflowLam0 sz z n : ℝ) : ℂ) else 0) ∧ (∀ u, GreenCore_Gc sz z n t ω u u ≠ 0)
```
**Pins** (`BAStab`, `BAGbEXPij'` and its three defs), probe `10fcef2` vs file, token diff of the whitespace-collapsed `def` blocks:
```
$ python3 pindiff.py RBM3D/Probe/T2390Pins.lean RBM3D/BA/GreenCore.lean
declarations compared: 5 (same names: True )
BAGbEXPij': identical
BAStab: identical
GreenCore_decayConcl: probe `(STblk` -> file `(Sizes.STblk`
GreenCore_decayConcl: probe `(STblk` -> file `(Sizes.STblk`
GreenCore_decayRHS: identical
GreenCore_loopPrem: identical
```
**Compiled nonempty instances** (namespace `GreenCoreInst`; `d = 3`, `sz0` at `n = 3`, `L = 16`, `W = 32768`, carrier from `flow_sz0` via `GreenCore_carrier`, `κ = 1/2`). `example` lines: 1659 1915 1917 1919 1921 1923 1925 1927 1930 1931 1932 1933 1934 1937 1938 1941 1943 1947 1953 1958 1962 1968 1973. R1 at `t = 1/2` for every `ω`; R2-R4 (incl. `GreenCore_Xstar` at line 1958, `GreenCore_Xi` at 1962, `φ ≡ 3`) at the zero sample `X = 0`, `t₁ = 10⁻¹¹ > 0`, where `G ≠ M` (`iΔ`, line 1902) and `BAStab … t₁ 256` is proved (`istabBA`, line 1861); `BAGbEXPij'` (line 1659) keeps the pin and `GreenCore_loopPrem` as hypotheses. Numbers (each also proved in Lean: `iwd`, `iC1n`, `Om`, `iLDE`, `(by norm_num)` for `hKδ`):
```
$ python3 numerics.py
W^-d = 2.842e-14 <= delta^2 = 4.000e-14: True | delta <= kappa/2: True | t1*3*L^d = 1.2288e-07 <= delta: True
(C1) 8 rho c0^-1 S theta = 0.2423 <= 1: True | K_BA = rho(1+rho2 K_Theta) = 1052672 | K_BA delta = 0.2105 <= 1/2: True
t1^2 #Vtx = 1.441e-05 <= Phi: True | phi = 3: loop <= 3^2 since |G| <= 3
```
**Name clash, diff, ports.**
```
$ M=$(git rev-parse --short main); c=0; while read n; do k=$(git grep -c -w -F "$n" $M -- RBM3D | wc -l); [ "$k" -ne 0 ] && echo "clash: $n" && c=$((c+1)); done < pub_after.txt; echo "public names checked: $(wc -l < pub_after.txt | tr -d ' '), names with any match on main ($M): $c"
public names checked: 88, names with any match on main (d859e60): 0
$ git diff --stat main...t/T2390     # main = d859e60
 RBM3D/BA/GreenCore.lean     | 1981 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2390Pins.lean  |  176 ++++
 RBM3D/Test/Axioms.lean      |    2 +
 docs/reports/T2390/inst.out |    4 +
 docs/reports/T2390/inst.py  |   14 +
 docs/reports/T2390/sz0.out  |    3 +
 docs/reports/T2390/sz0.py   |    7 +
 7 files changed, 2187 insertions(+)
$ grep -nE 'RBM1D|RBM2D' RBM3D/BA/GreenCore.lean; echo $?     # no port; this round read nothing under ../RBM1D, ../RBM2D
1
```
Files of 1b: `RBM3D/BA/GreenCore.lean`, `RBM3D/Test/Axioms.lean` (2 `owedProps` lines of the previous round). The probe and `docs/reports/T2390/*` are 1a files (never merged). `RBM3D.lean` is not changed on the branch.

**Narrative.**
1. This round delivers the scope gap of the previous round ((a′) D3.3): `GreenCore_Xstar` = (X*), `GreenCore_Xi` = (Ξ), with `GreenCore_T` (the kernel `T(a,c)`: the square root of the right side of (R*), rate `c₀/4`), `GreenCore_T_nonneg`, `GreenCore_Rsq` (right side of (R*) `≤ T²`), `GreenCore_Tshift` (`e^{-(c₀/4)|a-c|} T(a,a) ≤ T(a,c) ≤ e^{(c₀/4)|a-c|} T(a,a)`), `GreenCore_Qxd_eq` (`Q^{XD}_u = Σ_{l≠u} D_{lu} 𝔛_{ul}`).
2. Both are end-to-end on `Ω ∩ LDE`: their hypotheses are those of `GreenCore_Rbound` plus `hLrow` and `φ ≥ 0` (and for (Ξ) `0 ≤ t ≤ 1`, `hLquad`, `hLdiag`). Proofs: (X*) = (L1) (`Xrow_sq`) + (R*) (`Rbound`, `Rsq`) + `|G_{uy}| ≤ c₀⁻¹e^{-c₀|a-c|} + |Δ_{uy}|` + `R_{[u],u} ≤ (13/4)δ²` (`apriori`); (Ξ) = (E2) (`Arow_eq`) + `eps2_loc`, `eps1_loc`, `hLdiag`, and (X*) at the `2d` neighbours (`Tshift` at distance 1).
3. With these, every row of G.8 / (a′) for G3a is in the file: R1 (E0)-(E3), (E1′); R2 the local LDE bounds; R3 (m1), (R1) `twoSided`, (R*) `Rstar`/`Rbound`, (X*), (Ξ); R4 `coupled`, `diag`; R5 `BAStab`, `BAGbEXPij'`, registry lines, instances.
4. To stay under the stop line, the proofs of `conv1`, `conv2`, `closure`, `Rstar`, `twoSided`, `Acol_sq`, `apriori`, `Xrow_sq`, `Xcol_sq`, `Qxd_sq` are shorter and double blank lines are gone; no statement changed (two scripts above).
5. Inputs of (X*), (Ξ) about `M` are the C1-permitted ones: Kronecker `M`, `|M_{ab}| ≤ c₀⁻¹e^{-c₀|a-b|}`, `ℓ¹` rows `ρ`, `S`, `κ ≤ |m| ≤ 1`, `|M_{ab}| ≤ 1`; `g₀` enters through `D = g₀Ψ` (`hD`), `2dg₀` and `(C1)`, with no smallness of `g₀`.

## (c) Verified Mathlib names (`#check` in `lake env lean`, exit 0; 23 names; long types cut at 200 characters)
- `@Finset.sum_sq_le_sq_sum_of_nonneg : ∀ {ι : Type u_1} {R : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] {f : ι → R} {s : Finset ι}, (∀ i ∈ s, 0 ≤ f i) → ∑ i ∈ s, f i ^ …`
- `@Real.sq_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x ^ 2 = x`
- `@Real.sqrt_le_left : ∀ {x y : ℝ}, 0 ≤ y → (√x ≤ y ↔ x ≤ y ^ 2)`
- `@le_of_pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀} {n : ℕ} [MulPosMono M₀], n ≠ 0 → 0 ≤ b → a ^ n ≤ b ^ n → a ≤ b`
- `@Real.abs_le_sqrt : ∀ {x y : ℝ}, x ^ 2 ≤ y → |x| ≤ √y`
- `Real.exp_nat_mul : ∀ (x : ℝ) (n : ℕ), Real.exp (↑n * x) = Real.exp x ^ n`
- `@Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul : ∀ {ι : Type u_1} {R : Type u_2} [inst : CommSemiring R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) {r f g : ι → R…`
- `@norm_sub_norm_le : ∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (a b : E), ‖a‖ - ‖b‖ ≤ ‖a - b‖`
- `@div_mul_cancel₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {b : G₀} (a : G₀), b ≠ 0 → a / b * b = a`
- `@div_le_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}, 0 < c → (b / c ≤ a ↔ b ≤ a * c)`
- `@le_div_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}, 0 < c → (a ≤ b / c ↔ a * c ≤ b)`
- `@Finite.exists_max : ∀ {α : Type u_1} {β : Type u_2} [Finite α] [Nonempty α] [inst : LinearOrder β] (f : α → β), ∃ x₀, ∀ (x : α), f x ≤ f x₀`
- `@Finset.sum_le_sum_of_subset_of_nonneg : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι} [AddLeftMono N], s ⊆ t → (∀ i ∈ t, i ∉ s → 0 ≤ f…`
- `@Finset.single_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι} [AddLeftMono N], (∀ i ∈ s, 0 ≤ f i) → ∀ {a : ι}, a ∈ s → f a ≤ ∑ x …`
- `@Real.one_sub_inv_le_log_of_pos : ∀ {x : ℝ}, 0 < x → 1 - x⁻¹ ≤ Real.log x`
- `@sq_sum_le_card_mul_sum_sq : ∀ {ι : Type u_1} {α : Type u_2} [inst : Semiring α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] {s : Finset ι} {f : ι → α}, (∑ i ∈ s, f i) ^ 2 ≤ …`
- `@Finset.sum_mul_sq_le_sq_mul_sq : ∀ {ι : Type u_1} {R : Type u_2} [inst : CommSemiring R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) (f g : ι → R), (∑ i ∈ s, …`
- `@Finset.exists_max_image : ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] (s : Finset β) (f : β → α), s.Nonempty → ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x`
- `@inv_le_comm₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b : G₀}, 0 < a → 0 < b → (a⁻¹ ≤ b ↔ b⁻¹ ≤ a)`
- `@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀], 0 ≤ a → a ≤ b → ∀ (n : ℕ), a ^ n ≤ b ^ n`
- `@Matrix.submatrix_mul_equiv : ∀ {l : Type u_2} {m : Type u_3} {n : Type u_4} {o : Type u_5} {α : Type u_1} [inst : Fintype n] [inst_1 : Fintype o] [inst_2 : AddCommMonoid α] [inst_3 : Mul α] {p : T…`
- `@Ring.inverse_mul_cancel : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] (x : M₀), IsUnit x → Ring.inverse x * x = 1`
- `@smul_eq_zero : ∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M] {r : R} {m : M} [Module.IsTorsionFree R M] [IsCancelMulZero R], r • m = 0 ↔ r = …`
- Verified absent (`Unknown constant`): `Real.sqrt_le'`, `Real.sqrt_add_le_add_sqrt`, `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`, `Real.sqrt_eq_iff`.

## (d) Open issues and paper-delta candidates
1. Instances: R2-R4 hold at the zero sample (`X = 0`), where `𝔛 = 0` and the LDE events hold for `t₁² #Vtx ≤ Φ`; a sample with `X ≠ 0` satisfying the LDE events is not exhibited (they are the probabilistic inputs of `baLDEin_holds`).
2. Loop identification (not proved here): `GreenCore_loop G a b = W^{-2d} Σ |G_{xy}|²` is the entrywise form of `𝓛^{(2)}_{(-,+),(a,b)}`; the pin premise `GreenCore_loopPrem` uses `(baFMz sz z).L n t ![false,true] ![a,b]`. Linking `φ` of `Rbound`/`Xstar`/`Xi` to the pin is G4/G6.
3. Owed pins: `BAGbEXPij'` (owner G4, consumers G6a/G6b), `BAStab` at all `BAReal` data with `K_Θ = 16κ⁻⁴` (G3b); here `BAStab` is proved only at the instance data.
4. Candidates (the dispatcher numbers them):
   - `T2390l` (X*): `|𝔛_{uy}| ≤ (2Φ)^{1/2}((1 + 2/(κc₀)) T([u],[y]) + 13^{1/2}κ⁻¹δ|Δ_{uy}|)` for all `u, y` (also `u = y`); `T` has the coefficients `(4c₀⁻²SW^{-d})^{1/2}`, `(16ρΦc₀⁻¹S)^{1/2}` of `GreenCore_Rbound` and the rate `c₀/4` in `zdistD`. (a′) D3.3 has `C_XΦ_N[…] + 3κ⁻¹a|Δ_{uy}|`; here the `|Δ|` coefficient is `26^{1/2}κ⁻¹Φ^{1/2}δ` because the a priori bound `R_{[u],u} ≤ (13/4)δ²` includes the entry at the offset of `u`.
   - `T2390m` (Ξ): `|A_w + t v̄_{[w]}| ≤ 13^{1/2}κ⁻¹δ(1 + (2Φ)^{1/2})T + (2Φ)^{1/2}φ(b',b') + (ΦW^{-d})^{1/2} + (2Φ)^{1/2}((1 + 2/(κc₀))e^{c₀/4}2dg₀T + 13^{1/2}κ⁻¹δΣ_l|D_{lw}||Δ_{wl}|)`, `T = T(b',b')`; (a′) has `C_ΞΦ_N[…] + 3dg₀κ⁻¹aΣ_{l∈N(w)}|Δ_{wl}|`; the neighbour coefficient here is `26^{1/2}κ⁻¹g₀Φ^{1/2}δ` per neighbour.
   - The prover-max round's `T2390h`, `T2390j`, `T2390k` stand (statements unchanged): `h` the constants of (R*)/(C1) (`ϑ = GreenCore_theta`, `ρe = c₀⁻¹S`); `j` `GreenCore_diag` concludes `‖G-M‖² ≤ 8K²((9/4)A_b + X_b)` with a uniform loop bound `hLm` instead of the printed `≺` form; `k` `BAStab` is the max-norm stability statement without forming `(1-tM^{(+,+)})⁻¹`. Its `T2390i` ((X*), (Ξ) not in G3a's file) is withdrawn.
