Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 02:53:26 UTC 2026

Notation (d=3 in the instance). `Cm := mk sz (fun _ => E)`, `S := Cm.S n`, `m := Cm.m n`, `ξ_σ := u·m_{σ0}m_{σ1}` (`STmsigg`), `Θ := Step2Gen_Theta S ξ_σ = Ring.inverse(1-ξ S)` (`Chain/Step2Gen.lean:191-201`), `P(r) := tailW d L (sz.lam n) u ℓ W D r` (so `STprof = W^{-d}P`), `𝒯 = tailT`, `g = sz.lam n`. Mathematics only: the proof of `nkl_at` (`Induction/NewKLK.lean:993-1196`) is read with `S`, `Θ`, `K`, `LM`, `GMM`, `m` abstract. Layout (A)/(B), private names to open, and line predictions (ticket (i), (iv), (v)) are not stage-1a content and are not given here.

### (i) Exponent / constant table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `δ₀` | `κ/2` | Ward step `Im G_xx ≤ Im m+δ₀ ≤ 2 Im m` iff `δ₀ ≤ Im m` (`NewKLK.lean:767-785`, `Ind.half_le_mE_im`) | needs `Im m ≥ κ`: slack `Im m-κ/2 ≥ κ/2`; instance `Im m=1`, `δ₀=0.05` |
| 2 | **(H-Im)** domain fact | `∀ sz n E, 0<lam n ≤ 𝔡⁻¹, |E|≤2-κ ⟹ κ ≤ Im m` (as in the pin's quantifiers, `Step2Gen.lean:891-893`) | band: `m=mE E`, `Im ≥ √(κ(4-κ))/2 ≥ κ`; **BA: not implied** (script (b-a): `g=10, E=1: Im m = 0.0000 < κ=0.1`) | band: yes; BA: fails for large `g ≤ 𝔡⁻¹` (see Verdict) |
| 3 | shift constant `C_s` | `2^{d-2}e` (`nkl_tailT_shift`, needs `ℓ_t ≥ 1`, `one_le_ellT`) | `𝒯(r') ≤ C_s 𝒯(r)` for `r ≤ r'+1` | `C_s=2e=5.4366` at `d=3` |
| 4 | `C_T` | `C_T(d)` of `ekPropTInf_holds` (`PropTInf.lean:534`), used at `(g,u,u)`: `Σ_x 𝒯𝒯 ≤ C_T/(1-u)·𝒯` | `0<g`, `0≤u≤t<1`, disjunction by `le_total` | model-free; instance: sampled sup `15.07` |
| 5 | **(H-S)** kernel facts | `S_{xy}≠0 ⟹ |x-y|_∞≤1`; `Σ_y‖S_{xy}‖ ≤ 1`; `‖S_{xy}‖=‖S_{yx}‖` (`nkl_conv_two`, `nkl_bound2`) | band `SB` (`nkl_SB_support`, `sum_norm_SB_row`, `SB_transpose`); BA `S=1` (`BA/FlowPins.lean:327`) | band row sum `1.0000`, symmetric, support ≤1 (script (a)) |
| 6 | **(H-m)** | `‖m‖ ≤ 1` (so `|ξ_σ| ≤ u<1`, `|m_{σ0}m_{σ1}|≤1`) | band `‖mE‖=1`; BA: `BAPropM` `‖m‖≤1` (`BA/MFixedPoint.lean:575`, a pin owed by BA-D3/D4) | BA instance `|m|=0.99927`, `1-|m|²=1.46e-3` |
| 7 | **(H-conv)** `Θ`-convolution (replaces `nkl_theta_tail`+`nkl_SBTheta_*`+`nkl_conv_P`) | `∀ ℓ≥0, D≥0, a,a': Σ_b ‖(SΘ)(a,b)‖·P(|b-a'|_∞) ≤ (K_c/(1-u))·P(|a-a'|_∞)`, all four `σ` | band: `K_c = C₁C_s C_T+C_s` (`hK1`, `NewKLK.lean:1054-1060`, `C₁=C₅e^{1/(4c)}`, `Prop5Decay`). BA, `S=1`: `SΘ=(1-ξ)⁻¹I`, `K_c=1` from `|ξ|≤u` (row 6) | band measured `K_c·`=`1.0010`; BA `max(1-u)/|1-ξ|`: `1.0000, 0.9985, 0.8736, 0.0641` at `u=1/32,0.5,0.99,0.9999` |
| 8 | **(H-K)** marginals of `𝒦^{(2)}` | `∀σ,a: Σ_x‖K n u σ ![x,a]‖ ≤ C_K W^{-d}/(1-u)`, same in the second slot | band `C_K=1` (`nkl_ward_K`, `Θ` transpose-symmetric + row sums). BA: `K=W^{-d}(Θ^{σσ'}M^{σσ'})` (`BA/KSolve.lean:63-66`), `Σ_b|M^σ_{ba}M^{σ'}_{ab}|≤1` by Cauchy-Schwarz and `Σ_b|M_ab|²=1` (`BAPropM`), Neumann series in `ℓ¹`, `C_K=1` | BA measured `max (1-u)·rowsum = 1.0000` for `u` up to `0.9999` |
| 9 | **(H-L)** link `LM`/`GMM` to resolvent | `∃ ζ:ℝ→ℂ`: `LM n u H σ a = loopFine d L W H (ζ u) σ a`, `Im ζ(u) = (1-u) Im m`, `GMM n u H x x = Gres H (ζ u) true x x - m` (diagonal only) | band `ζ=zt E`, `zt_im`; BA: `BALloop = loopFine(...)(ztOf ..)` (`FlowPins.lean:264`), `M_xx=m₀` (`BAMB_diag_eq`, `Ward.lean:89`); no `M=mI` needed | `η=(1-u)Im m>0`; instance `η=31/32` |
| 10 | Ward marginals of `𝓛^{(2)}` | `Σ_x‖L(x,a₁)‖ ≤ 2W^{-d}(Im m+δ₀)/η ≤ 4W^{-d}/(1-u)` (`nkl_ward_L`, `Σ_j|G_lj|²=Im G_ll/η`) | needs `H` Hermitian (given by the pin), rows 1, 9 | instance: `|G|²=Im G/η=1.0656` |
| 11 | `Σ̄` | `(4+C_K)W^{-d}/(1-u)` (band `5`) | row 8 + 10 | band `4+1=5` |
| 12 | final `C` | `C = 2K_c + 2C_s(4+C_K) + C_s C_T` (band: `2(C₁C_sC_T+C_s)+10C_s+C_sC_T`, `NewKLK.lean:1001`) | depends on `d` and the constants of rows 4, 7, 8 only; `1_{ℓ≥1}` term via `nkl_conv_two` | instance: needed `max=1.876`, proof constant `138.3` |
| 13 | profile positivity | `P>0`, `P(r) ≥ W^{-D}`; `J ≥ 0` (`hJ0`) | `W>0`, `ℓ ≥ 0` | none |
| 14 | pin quantifiers | `0<lam`, `lam≤𝔡⁻¹`, `|E|≤2-κ`, `0≤u<1`, `0≤D`, `0≤ℓ≤L` | used: `0<g` (row 4), `u<1` (all `(1-u)⁻¹`), `|E|≤2` only through row 2 | `lam≤𝔡⁻¹` is not used by the generic proof (only by band `Prop5Decay` inside row 7) |

Consequences: (a) the generic proof reads `K` only through row 8, `S` and `Θ` only through rows 5-7, `GMM`/`LM` only through rows 9-10; it never reads `‖m‖=1`, `M=mI` or `mSigma`. (b) the floor-free `𝒦^{(2)}` tail `‖K‖≤C₁W^{-d}𝒯_u` of the ticket's list is **not read** by the proof: `K` enters only through its marginals (row 8) and `Ĵ=STJhatMg`; the tail is the input of a sum-of-tail lemma `Σ_x𝒯_u(|x-a|_∞) ≤ c_d/(1-u)` (shell count, `ℓ_u²≤max(g²/(1-u),1)`), which would give row 8 from the tail; I found no merged lemma with this conclusion by `grep` of `Σ … tailT` and did not derive it, so row 8 is stated as the hypothesis. (c) `Step2K2.lean` has one public declaration, `stK2decay_holds` (`:132`); no other generic form is needed.

### (ii) One concrete nondegenerate instance and external-hypothesis limits

Band instance (target 2 re-derivation): `d=3`, `n=0` of `sz0`: `L=4`, `W=32`, `lam=1/64`, `κ=𝔡=1/10`, `E=0` (`m=i`), `u=1/32`, `D=1`, `ℓ∈{0.5, 2}` (indicator off/on), `H=0` (Hermitian), `‖G_u-M‖_max=u/(1-u)=1/31 ≤ δ₀=1/20`. Script checks rows 5, 7, 8, 10, 12 and then the two pin inequalities directly (`thetaOp(LK)` and `ELKLK`, all `σ`, `a` on a grid of `Z_4^3`, with `STprof`, `Ĵ` computed from the explicit `LM=G_{σ0}G_{σ1}W^{-d}δ_{ab}`, `K=W^{-d}mm'Θ`).
```
$ python3 scratchpad/T2405/band.py
S: row sum 0.9999999999999999 sym 0.0 support Linf<=1 True
measured C_T (TTT2, (1-u) factor): 15.072189785513583
max (1-u) sum_b|S Theta(a,b)| = 1.0000000000000002 (<=1)  ; max |S Theta|/T_u = 0.9833727620321675
measured K_conv (conv bound x (1-u)): 1.0009565148518227
||G-M||_max = 0.032258064516129004 = u/(1-u) = 0.03225806451612903  delta0=kap/2= 0.05  Im G= 1.032258064516129  2 Im m= 2.0
row mass |G|^2 = 1.0655567117585847   Im G/eta = 1.0655567117585847
l=0.5: J=0.09142  C needed: bound1 1.876, bound2 0.09269; proof constant C=2K_conv+2Cs(4+C_K)+Cs*C_T = 138.3  ok=True
l=2.0: J=0.09142  C needed: bound1 1.876, bound2 0.08492; proof constant C=2K_conv+2Cs(4+C_K)+Cs*C_T = 138.3  ok=True
```
(`C_T` and `K_conv` are sampled maxima over `a ∈ {0,7,14,…}` / `a ∈ {0,5,…}`, not proved suprema; `(1-u)·row sum = 1` shows the row-sum bound `(1-u)⁻¹` is attained, no slack. The instance has `J>0`, `G_u≠M`.)

BA instance (external hypotheses rows 2, 6, 7, 8, which BA-D3/D4, `BAKsolve` and the BA carrier owe). Limit computations (TEAM §8 lesson 14): (b-a) `Im m` at the pin's domain `|E|≤2-κ=1.9` for growing `g` (`d=3`, `L=16`, exact eigenvalues of `gΨ^{(B)}`, `m=L^{-d}Σ_k(gλ_k-E-m)⁻¹`); (b-b) real-axis BA data at `L=4`, `g=1/64`, `E=0`, `S=1`: `|m|`, `Σ_b|M_ab|²`, `1-|m|²`, row 8 and row 7 constants as `u→1`.
```
$ python3 scratchpad/T2405/ba.py
(a) domain of Im m >= kappa=0.1 at |E|<=2-kappa, d=3, L=16 (eigenvalues exact), Im m at:
  g=0.01562  E= 0.0: 0.9993 E= 1.0: 0.8656 E= 1.9: 0.3141
  g=1        E= 0.0: 0.4160 E= 1.0: 0.4057 E= 1.9: 0.3801
  g=10       E= 0.0: 0.2028 E= 1.0: 0.0000 E= 1.9: 0.0714
(b) m= (-1.734723475976807e-18+0.9992690922023455j)  |m|= 0.9992690922023455  diag(M)=m: True  sum_b|M_ab|^2= 1.000000000000003  1-|m|^2= 0.0014612813691002868  1-|m|^2 / g^2 = 5.985408487834775
  u=0.03125: max (1-u) rowsum|K W^d| = 1.0000 (C_K<=1) ; max (1-u)/|1-xi| = 1.0000 (K_conv<=1) ; max |1-xi|^-1 / B_u0 = 0.9848
  u=0.5    : max (1-u) rowsum|K W^d| = 1.0000 (C_K<=1) ; max (1-u)/|1-xi| = 0.9985 (K_conv<=1) ; max |1-xi|^-1 / B_u0 = 0.9837
  u=0.99   : max (1-u) rowsum|K W^d| = 1.0000 (C_K<=1) ; max (1-u)/|1-xi| = 0.8736 (K_conv<=1) ; max |1-xi|^-1 / B_u0 = 0.8808
  u=0.9999 : max (1-u) rowsum|K W^d| = 1.0000 (C_K<=1) ; max (1-u)/|1-xi| = 0.0641 (K_conv<=1) ; max |1-xi|^-1 / B_u0 = 0.2092
```
Reading: (b-b) `|m|≤1`, `Σ|M|²=1`, `1-|m|²≈6g²>0`; `C_K=1` and `K_c=1` hold for `u` up to `0.9999` (so rows 6-8 are consistent at BA, with `K_c=C_K=1`); the last column shows the `SΘ` **tail** form `|(SΘ)(a,a)| ≤ C𝒯_u(0)` would also hold at `S=1` (ratio `<1`) because `1-|m|²≳g²`, but the **conv** form (row 7) needs only `|m|≤1`, so I recommend row 7 in conv form (no `1-|m|²≳g²` input). (b-a) `Im m` falls below `κ=0.1` inside `|E|≤1.9` (`g=10`, `E=1`: `0.0000`; `g=10,E=1.9`: `0.0714`), and `𝔡=1/10` allows `lam` up to `𝔡⁻¹=10` (`STNewKLKAtgL` hypotheses `0<lam≤𝔡⁻¹`, `|E|≤2-κ`).

### Verdicts
- **Target 1 `stNewKLKAtgL_of` (generic, `δ₀=κ/2`): PASS** as a conditional theorem under rows 2, 5-9 (hypotheses over `mk`), `C` as in row 12, depending on `(d, 𝔡)` only through the constants of the hypotheses. All exponent rows close; the instance satisfies every deterministic hypothesis with no collapse (`J=0.0914`, `u=1/32`, `ℓ=2`).
- **Target 2 `stNewKLKgL_of`: PASS**, same hypotheses quantified as the pin quantifies `κ 𝔡` (each row is `∀ κ 𝔡, 0<κ → 0<𝔡 → …`, with the constants allowed to depend on `(κ,𝔡)`).
- **Target 3 (BA-dischargeability, C1): rows 5-9 are C1-clean (stated through `mk`: `S`, `m`, `K`, `LM`, `GMM`) and have BA sources (rows 6-9: `BAPropM`, `BAKsolve`, `FlowPins.lean:264,327`, `BAMB_diag_eq`); none is merged as a BA theorem, they are owed by BA-D3/D4, `BAKsolve`, and the BA `Step2Mat` instance (not yet in `main`).** One exception, **row 2 (H-Im) is not dischargeable at BA for all `sz` of the pin's domain** (script (b-a), finite `L=16`, hence an indication, not a proof): `|E|≤2-κ` and `lam≤𝔡⁻¹` do not give `Im m ≥ κ` at BA. This does not block T2405 (the generic theorems take row 2 as an argument), but T3-BA cannot prove `STNewKLKgL` at BA from it; the dispatcher should decide between (1) a primed pin `STNewKLKAtgL'` with the extra premise `κ ≤ Im (Cm.m n)` (new statement, `STNewKLKAtgL` unchanged), or (2) discharging row 2 at BA only on a restricted `lam` range, with `STNewKLKgL` at BA left owed.
- **Observation (paper-delta candidate T2405a):** at the BA carrier `S=1`, so the generic `STthetaOpg` (`Step2Gen.lean:191-201`) is the diagonal operator `Σ_i m m'(1-ξ)⁻¹A(a^{(i)}(a_i))`, not the BA propagator `BATheta=(1-uM^{σσ'})⁻¹` (`BA/MFixedPoint.lean:515`) that appears in `𝒦^{(2)}` (`KSolve.lean:66`); the pin at BA is the statement for the diagonal operator. This is as pinned in T2386 (merged) and not changed here.
- **Not assessed here (stage-1a rules):** layout (A)/(B), opened private names, line counts against the stop line 900.

## (a′) Preflight corrections — Sun Oct 11 03:45:39 UTC 2026

Amend 1 (`docs/tickets/T2405-amend-1.md`, D1-D4) answers the 1a-audit (`T2405-1a-audit.md`). Section (a) is not edited. For this design gate the ticket's items (i), (iii), (iv), (v) override the generic 1a format (D4). Stage 1a writes no Lean: statements are given as a diff against the merged text and in mathematical form with the carrier's field names. Scripts: `scratchpad/T2405/{cone,layout,aprime,band_corollary}.py`.

### C1. Corrections to (a)
- **Rows 1, 2 (D1, D2).** `δ₀ = κ/2 ≤ κ ≤ Im m`: the primed premise `κ ≤ Im (mk sz (fun _ => E)).m n` is the carrier datum (`BAReal`, `BA/MFixedPoint.lean:432`). The false band claim `Im ≥ √(κ(4-κ))/2 ≥ κ` is dropped. The band uses `κ/2 ≤ Im mE` (`Ind.half_le_mE_im`, `Induction/ConArgDet.lean:746`; hypotheses `0 ≤ κ`, `|E| ≤ 2-κ`). The (b-a) finding of (a) (BA `Im m < κ` inside `|E| ≤ 2-κ`) is moot: the primed pin carries `κ ≤ Im m` as a premise, not as a consequence of `|E| ≤ 2-κ`.
- **Row 6 BA source.** (a) says "`BAPropM` is a pin owed by BA-D3/D4"; that was the docstring (`BA/MFixedPoint.lean:566`). `baPropM_holds (d Λ κ) : BAPropM d Λ κ` is proved (`BA/CombesThomas.lean:562`; `grep sorry` on the file: no hit), and `BAPropM` contains `‖m‖ ≤ 1` and `∑_b‖BAMB a b‖² = 1` (`MFixedPoint.lean:567-575`).
- **Row 8 BA source.** (a) gave "Cauchy-Schwarz and Neumann series". Merged pieces: `(Kn2sol)` is `baKsolve` (`BA/KTreeRep.lean:1699`, statement `BAKsolve` `BA/KSolve.lean:58-66`); `∑_b|Θ^{(s,s')}(a,b)| ≤ (1-t)⁻¹` and the column form are the private `KWardIneq_theta_row_le` / `_col_le` (`BA/KWardIneq.lean:255`, `:265`) from `BAK_row_sum` / `BAK_col_sum` (`BA/KKernel.lean:124`, `:128`). What is not merged is the product `Θ·M^{(σσ')}` row/column bound and the link `BAKloop = BAKsol` at `n = 2`: owed to T3-BA (BA-T pin REQ, supervisor 1155 C7), no BA proof here (Amend 1).
- **Instance of (a).** At `δ₀ = κ/4` (the unprimed route of D1′) `u = 1/32` is too large (`u/(1-u) = 0.0323 > 0.025`). The corollary route uses `u = 1/64` (script below); the primed route keeps `u = 1/32`.
- **D3 (T2404).** T2404's (HK) (`T2404-prove.md:20`) is the far bound `‖K^{(2)}‖ ≤ W^{-(2d+D)}` for `|x-x'|_∞ ≥ ℓ*`. T2405's row F8 below is the marginal bound `∑‖K^{(2)}‖ ≤ C_K W^{-d}/(1-u)`. They are different inputs; T2405 does not read the 2-loop tail, so the ticket's coordination sentence does not apply.

### C2. Checks of D1-D2 (script output)
```
$ python3 -I scratchpad/T2405/aprime.py
D2  kappa/2<=Im mE on |E|<=2-kappa: violations 0  min(Im mE - kappa/2) = 0.0005   (grid; equality at kappa=2)
D1  kappa<=Im mE with |E|>2: counterexamples 0                                      (so the primed premise forces |E|<=2 at the band)
Ward step: violations 0                       ((Im m+kappa/2)/((1-u)Im m) <= 2/(1-u) when kappa<=Im m)
constants: max |generic - band| = 0           (2Kc+2Cs(4+CK)+Cs*CT = 2(C1*Cs*CT+Cs)+10Cs+Cs*CT at Kc=C1*Cs*CT+Cs, CK=1)
BA conv constant K_c: max (1-u)/|1-xi| = 0.99999   (S=1, Theta=(1-xi)^-1 I, |xi|<=u)
primed, delta0=kappa/2 : 0<lam True lam<=1/dd True kp<=Im m(E) True 0<=u<1 True 0<=D True 0<=ell<=L True |G-M|=u/(1-u)=0.03226 <= delta0=0.05000 True | dom ...: True
unprimed via kappa'=kappa/2, delta0=kappa/4 : ... kp<=Im m(E) True ... |G-M|=u/(1-u)=0.01587 <= delta0=0.02500 True | dom |E|<=2-kappa and kappa/2<=Im m: True
$ python3 scratchpad/T2405/band_corollary.py      # band.py of (a) with u=1/64, delta0=kappa/4
||G-M||_max = 0.015873015873015817 = u/(1-u) = 0.015873015873015872  delta0=kappa/4= 0.025  Im G= 1.0158730158730158  2 Im m= 2.0
l=0.5: J=0.04591  C needed: bound1 1.936, bound2 0.04655; proof constant C=138.3  ok=True
l=2.0: J=0.04591  C needed: bound1 1.936, bound2 0.04451; proof constant C=138.3  ok=True
```
The `κ ≤ 2` needed for `κ/2 ≤ Im mE` on the whole domain follows from `|E| ≤ 2-κ`: at `E = ±(2-κ)`, `Im mE = √(κ(4-κ))/2 ≥ κ/2` iff `κ ≤ 2` (`mE_im`, `Defs/Semicircle.lean:42`).

### C3. (iii) The generic statements (as a diff and in mathematics)
Notation. `Cm := mk sz (fun _ => E)`, `g = sz.lam n`, `W = sz.W n`, `L = sz.L n`, `ξ_σ = u·STmsigg Cm n (σ 0)·STmsigg Cm n (σ 1)`, `SΘ_σ := Cm.S n * Step2Gen_Theta (Cm.S n) ξ_σ`, `P(r) := tailW d L g u ℓ W D r`. **Premise bundle Π(sz,n,E,u)**: `0 < g`, `g ≤ 𝔡⁻¹`, `κ ≤ Im (Cm.m n)`, `0 ≤ u`, `u < 1` (the pin's premises with `|E| ≤ 2-κ` replaced by D1). Every fact F5-F9 is a hypothesis "∀ sz n E u, Π → …".
- **`STNewKLKAtgL'`** (pin, new; name from D1): the text of `STNewKLKAtgL` (`Chain/Step2Gen.lean:889-902`) with the single binder `|E| ≤ 2 - κ →` replaced by `κ ≤ ((mk sz (fun _ => E)).m n).im →`. **`STNewKLKgL'`**: the text of `STNewKLKgL` (`:903-904`) with `STNewKLKAtgL'`.
- **Target 1 `stNewKLKAtgL'_of`** (name adjustable): for `3 ≤ d`, `κ, 𝔡 > 0`, `K_c, C_K ≥ 0`, a family `mk : ∀ sz, (ℕ → ℝ) → Step2Mat sz` and F5-F9, `∃ C > 0, STNewKLKAtgL' d κ 𝔡 C (κ/2) mk`, with `C = 2K_c + 2C_s(4+C_K) + C_s C_T`, `C_s = 2^{d-2}e`, `C_T` from `ekPropTInf_holds d` (`Evolution/PropTInf.lean:534`).
  - **F5** (`S`): `Cm.S n x y ≠ 0 → zdistInf d L (x-y) ≤ 1`; `∑_y ‖Cm.S n x y‖ ≤ 1`; `‖Cm.S n x y‖ = ‖Cm.S n y x‖`.
  - **F6**: `‖Cm.m n‖ ≤ 1`.
  - **F7** (conv): `∀ σ ℓ' D' a a'`, `0 ≤ ℓ'`, `0 ≤ D'`: `∑_b ‖SΘ_σ a b‖ · tailW d L g u ℓ' W D' |b-a'|_∞ ≤ K_c/(1-u) · tailW d L g u ℓ' W D' |a-a'|_∞`.
  - **F8** (K): `∀ σ : Fin 2 → Bool`: `∀ a₁, ∑_x ‖Cm.K n u σ ![x,a₁]‖ ≤ C_K (W^d)⁻¹ (1-u)⁻¹` and `∀ a₀, ∑_y ‖Cm.K n u σ ![a₀,y]‖ ≤` the same.
  - **F9** (link): `∃ ζ : ℂ, ζ.im = (1-u)·Im(Cm.m n) ∧ (∀ H σ a, Cm.LM n u H σ a = loopFine d L W H ζ σ a) ∧ (∀ H x, Cm.GMM n u H x x = Gres H ζ true x x - Cm.m n)`.
- **Target 2 `stNewKLKgL'_of`**: `STNewKLKgL' d mk` from F5, F6, F9 and the form `∀ κ 𝔡 > 0, ∃ K_c C_K ≥ 0, F7 ∧ F8` (the pin's `∃ C δ₀` is after `∀ κ 𝔡`); proof: target 1 at `δ₀ = κ/2`.
- **Target 2′ (D1′, unprimed corollaries)**: (a) `STNewKLKAtgL d κ 𝔡 C (κ/4) mk` from `STNewKLKAtgL' d (κ/2) 𝔡 C (κ/4) mk` and the domain fact `dom_κ`: `∀ sz n E, 0 < g → g ≤ 𝔡⁻¹ → |E| ≤ 2-κ → κ/2 ≤ Im (Cm.m n)`; (b) `STNewKLKgL d mk` from `STNewKLKgL' d mk` and `∀ κ 𝔡 > 0, dom_κ`. Band: `dom_κ` is `Ind.half_le_mE_im`; then `(bandStep2_STNewKLK d).mpr` (`Step2Gen.lean:919`) gives `STNewKLK d`. `NewKLK.lean` is not edited by (A); under (B) the public band statements are unchanged (G1).
- **`rfl` / `Iff.rfl` analysis** (predicted from the merged definitions, not compiled; 1b tests each):
  - Succeed, as merged bridges: `STLMg/STLKMg/STJhatMg/STELKLKMg/STthetaOpg/STGMMg = band` (`Step2Gen.lean:228-248`, all `:= rfl`); `STprof sz n u D ℓ x y = (W^d)⁻¹ P(|x-y|_∞)` (`NewKLK.lean:1012`); `Theta d L g ξ = Step2Gen_Theta (SB d L g) ξ` (unfold both, `Ring.inverse (1 - ξ • SB)`); `(bandStep2Mat sz E).K n u σ a = STKloop sz n (E n) u σ a` (`Carrier.lean:205`); `STmsig E s = mSigma E s` (`NewKLK.lean:987`).
  - **Fail 1.** `STNewKLKAtgL' … ↔ STNewKLKAt …` is not `Iff.rfl` (premise `κ ≤ Im m` against `|E| ≤ 2-κ`); the band pin is recovered by the corollary of 2′ and `bandStep2_STNewKLK`.
  - **Fail 2.** `GMM` on the diagonal at the band: `STGMM` ends in `if x = y then mE E else 0` (`Step2Defs.lean:146-148`), which does not reduce at `y := x` by `rfl`; use `simp [STGMM]` (as `NewKLK.lean:778-782`) for F9's last clause.
  - **Fail 3.** `((mk sz fun _ => E).m n)` at `mk = fun sz E => bandStep2Mat sz E` is `mE E` by beta and projections, but `rw [mE_im]`, `rw [zt_im]` do not fire on it: use `show`/`change` first.
  - **Fail 4.** `STLMg Cm n u H σ a` and `STLKMg` are defs (`Step2Gen.lean:159-166`): a hypothesis `LM = loopFine …` needs `unfold STLKMg STLMg` before `rw`; `Cm.LM` carries an implicit `{k}`, fixed by the type of `σ`.
  - Statement-level BA example: `grep -rn baStep2 RBM3D` has no hit, so no BA `Step2Mat` family is merged; 1b builds a private family over `baFM sz sz.lam E` (`BA/FlowPins.lean:322-327`: `S := 1`, `m := BAmF …`) with `LM := loopFine … (ztOf (BAmF …) (E n) u)` and inert `LIM, KI, Pp, Hpath`; no BA fact is proved.

### C4. (ii) rows with sources (only the rows the audit asked to complete)
| fact | band source (file:line) | BA source or owing row |
|---|---|---|
| F5 | `nkl_SB_support` `NewKLK.lean:201`; `sum_norm_SB_row` `Defs/Block.lean:118` (equality, so `≤ 1`); `SB_transpose` `Defs/Block.lean:58` | `S := 1` `BA/FlowPins.lean:327`: support `x = y`, row sum `1`, symmetric; elementary, owed to T3-BA |
| F6 | `norm_mE` `Defs/Semicircle.lean:63` at `|E| ≤ 2`; `|E| ≤ 2` from `κ ≤ Im mE` and `mE_im` (`:42`, `√` of a negative is `0`) | `baPropM_holds` `BA/CombesThomas.lean:562` (`‖m‖ ≤ 1`) |
| F7 | `prop5Decay_holds` `Propagator/Prop5Hold.lean:784` + `nkl_theta_tail` `:226` + `nkl_SBTheta_tail` `:285`, `nkl_SBTheta_row` `:314` + `nkl_conv_P` `:334`, as `nkl_at` `:1035-1058`; `K_c = C₁C_sC_T + C_s` | `S = 1`: `SΘ = (1-ξ)⁻¹ I`, `|ξ| ≤ u` from F6, `|1-ξ| ≥ 1-u`, `K_c = 1`. No merged lemma; owed to T3-BA (the 1-line reduction above) |
| F8 | `nkl_ward_K` `NewKLK.lean:700` (`|E| ≤ 2`, `C_K = 1`) | `BAKsolve` `(Kn2sol)` `BA/KSolve.lean:63-66`, `baKsolve` `BA/KTreeRep.lean:1699`; `KWardIneq_theta_row_le/_col_le` `BA/KWardIneq.lean:255, :265`. Owed to T3-BA: the `Θ·M^{(σσ')}` marginals and `BAKloop = BAKsol` at `n = 2` |
| F9 | `ζ = zt E u`, `zt_im` `Defs/Semicircle.lean:182`; `STLM = loopFine … (zt E u)` `Step2Defs.lean:60-62`; diagonal by `simp [STGMM]` | `BALloop` `BA/FlowPins.lean:264`, `ztOf_im` `Loop/GLoopFlow.lean:64` (`etaOf m t = (1-t) m.im`, `:58`), `BAMB_diag_eq` `BA/Ward.lean:89`; the BA `Step2Mat.GMM` is owed to T3-BA |

### C5. (i) Layout, cone, (v) predicted lines, (iv) opened names
```
$ python3 -I scratchpad/T2405/cone.py        (main 3e72137; ticket's 84 / 95,136 = these + NewKLK itself: 83+1, 93,804+1,332)
RBM3D.Induction.NewKLK reverse cone: modules 83 lines 93804 LWExpCert* 6
RBM3D.Chain.Step2Gen reverse cone: modules 54 lines 45724 LWExpCert* 0
RBM3D.Induction.Step2K2 reverse cone: modules 99 lines 116247 LWExpCert* 6
Step2Gen in closure(NewKLK imports): False      NewKLK in closure(Step2Gen imports): False   (no cycle either way)
importers of Chain.NewKLKGen: 0 module exists: False     direct importers of NewKLK: NewKLKL, OptL2a, Step5Kit, Step5Pins
$ python3 -I scratchpad/T2405/layout.py
measured blocks: {'nkl_conv_P': 72, 'nkl_conv_two': 44, 'nkl_bound2': 142, 'nkl_ward_LKM': 62, 'nkl_at': 202}
lines mentioning SB/Theta: {'nkl_conv_P': 13, 'nkl_conv_two': 9, 'nkl_bound2': 25, 'nkl_ward_LKM': 0, 'nkl_at': 15}
lines mentioning band names: {'nkl_conv_P': 0, 'nkl_conv_two': 0, 'nkl_bound2': 0, 'nkl_ward_LKM': 17, 'nkl_at': 22}
(A) total 768   (new file: header 45, pins 22, copies conv_P 72 + conv_two 44 + bound2 148, ward_LKM 65, main proof 217, corollary 25, band instance 100, BA example 30)
(B) total 483   (in-place diff = insertions+deletions: conv_P 29, conv_two 21, bound2 56, ward_LKM 54, nkl_at 135, pins 22, corollary 25, band instance 100, BA example 30, import 11)
(A)-(B) = 285  ticket rule: (B) only if (A)-(B) > 150 -> (B)
stop line 900: (A) margin 132  (B) margin 417
```
Measured: block sizes and the SB/Theta and band-name line counts (the lines that change when `S`, `Θ`, `m`, `LM` become `mk` fields). Estimated: the sizes of new text (pins, corollary, band instance 100, BA example 30, headers). Reading: the copies of `nkl_conv_P`, `nkl_conv_two`, `nkl_bound2` (264 lines) are new text in (A) and about 106 diff lines in (B), because their `SB`/`Θ` become hypotheses over a free matrix `S`. The gap falls below 150 only if the (A) estimate were 135 lines (18%) too large; I do not expect that.
- **Layout.** By the ticket's rule the 1a selects **(B)** (`Induction/NewKLK.lean` in place, one added import `RBM3D.Chain.Step2Gen`, acyclic per script; no `RBM3D.lean` edit); the merge then joins the certificate lane (reverse cone 84 modules, six `Graph/LWExpCert*`, 52-62 min, H176). **(A) is feasible** (768 ≤ 900, zero importers, no certificate rebuild); if the dispatcher prefers (A) for the merge cost, the list below applies. Both fit the stop line 900.
- **(iv) Private names to open under (A)** (`open private … from RBM3D.Induction.NewKLK`, before `namespace`; they then resolve under `RBM.Gauss.Sizes`, so the file has `open RBM.Gauss.Sizes` as `Step2Gen.lean:47`; precedent `DuhamelII.lean:42`, `EMn2Exp2.lean:47-53`). Spans from `layout.py`; copying a name costs its span. Under (B): none.
  - generic proof (173 lines not copied): `nkl_Cs_ge_one` (:112, 5), `nkl_tailT_shift` (:72, 38), `nkl_tailT_le_tailW` (:118, 4), `nkl_tailW_eq_of_near` (:123, 6), `nkl_tailW_far` (:131, 37), `nkl_zdistInf_sub_comm` (:180, 2), `nkl_zdistInf_tri` (:194, 5), `nkl_dist_cases` (:831, 6): tail shift/near/far and distance facts that the copies of `nkl_conv_P/two/bound2` use as is; `nkl_ward_L` (:623, 55): generic in `H, z` (already `Gres`/`loopM`); `nkl_gres_blockMat_true` (:740, 15): turns `Gres (blockMat H)` into `Gres H` in the `hdiag` step.
  - band instance only (219 lines not copied): `nkl_theta_tail` (:226, 49), `nkl_SBTheta_tail` (:285, 28), `nkl_SBTheta_row` (:314, 18), `nkl_conv_P` (:334, 72), `nkl_SB_support` (:201, 11), `nkl_ward_K` (:700, 40), `nkl_STmsig_eq` (:987, 1): the discharge of F5, F7, F8 at the band.
- **(v) Predicted lines**: (B) 483, (A) 768, against stop line 900; reserve for unknowns in (A) 132, in (B) 417.

### C6. Verdicts after Amend 1
- **Target 1 `stNewKLKAtgL'_of`: PASS** (all exponent rows close; C2, row 12 unchanged; band and BA instances satisfy the premises: C2).
- **Target 2 `stNewKLKgL'_of`: PASS.**
- **Target 2′ (unprimed corollaries via `κ' = κ/2`): PASS**; `δ₀ = κ/4`; `dom_κ` is `Ind.half_le_mE_im`.
- **Target 3 (BA dischargeability, C1): PASS** for the statements: F5-F9 are through `mk` only, with the premise `κ ≤ Im m` that `BAReal` carries; each has a merged source or an owing T3-BA row (C4); none of these rows is proved here.
- **Target 4: PASS** (`stK2decay_holds` is the only public declaration of `Step2K2.lean`, `:132`).
- **Target 6:** band `example` PASS (discharge list in C4); the BA statement-level `example` needs a private `Step2Mat` family (C3, last bullet), no BA fact.
- **Layout: (B) by the ticket's rule (285 > 150); (A) feasible.** No hypothesis set fails, no exponent fails, nothing is BLOCKED.
- **Paper-delta candidates:** T2405a (S = 1 at BA, `STthetaOpg` is the diagonal operator, not `BATheta`; (a) Observation); **T2405b**: the primed pin replaces the paper's `|E| ≤ 2-κ` (`lem:newKLK`, `3_5:371-378`) by the datum `κ ≤ Im m`; the unprimed pins are corollaries (D1′).

## (b) Script output — stage 1b (`prover-hard`, Amend 1), layout (A)
Layout and cone: (A) new `RBM3D/Chain/NewKLKGen.lean` (`namespace RBM.BA`); zero importers, so the merge rebuilds no certificate module; `Induction/NewKLK.lean`, `Induction/Step2K2.lean` and `RBM3D.lean` are not edited (the root import is the hub's, CLAUDE.md §3 (A) 4).
Lines: 816 against the stop line 900 (`wc -l` run before each of the four commits: 810, 815, 814, 816; (a′) C5 predicted (A) 768).
Hypothesis table as finally used (`NewKLKGenHyp`, all through `mk`; BA sources and owing rows as in (a′) C4, none proved here):
| fact | content | band discharge (new file lines) | BA source / owner |
|---|---|---|---|
| F5 | `S`: support `|x-y|_∞ ≤ 1`, row sums `≤ 1`, symmetry | :681-687 (`nkl_SB_support`, `sum_norm_SB_row`, `SB_transpose`) | `S = 1` `FlowPins.lean:327`; T3-BA |
| F6 | `‖m‖ ≤ 1` | :688-690 (`norm_mE`; `\|E\| ≤ 2` from `κ ≤ Im mE`) | `baPropM_holds` `BA/CombesThomas.lean:562` |
| F7 | `Σ_b ‖(SΘ_σ)(a,b)‖ 𝒯̃(\|b-a'\|) ≤ K_c/(1-u) 𝒯̃(\|a-a'\|)` | :691-720 (`prop5Decay_holds`, `nkl_theta_tail`, `nkl_SBTheta_*`, `nkl_conv_P`, `ekPropTInf_holds`; `K_c = C₁C_sC_T+C_s`) | `S = 1`: `K_c = 1` from `\|ξ\| ≤ u`; T3-BA |
| F8 | `Σ_x‖K_{(x,a₁)}‖`, `Σ_y‖K_{(a₀,y)}‖ ≤ C_K W^{-d}/(1-u)` | :721-724 (`nkl_ward_K`, `C_K = 1`) | `baKsolve`, `KWardIneq_theta_*`; T3-BA owes `Θ·M^{σσ'}`, `BAKloop = BAKsol` |
| F9 | `LM`, diagonal `GMM` are `loopFine`, `Gres - m` at `ζ`, `Im ζ = (1-u) Im m` | :725-731 (`zt_im`, `rfl`, `simp`) | `BALloop` `FlowPins.lean:264`, `BAMB_diag_eq` `Ward.lean:89`; T3-BA |
```
$ date -u; git log --oneline -1; git diff --stat main...t/T2405 | head -1; wc -l RBM3D/Chain/NewKLKGen.lean   # stop line 900; RBM3D.lean untouched
Sun Oct 11 04:14:58 UTC 2026
50818fe T2405: source line references in the header
 RBM3D/Chain/NewKLKGen.lean | 816 +++++++++++++++++++++++++++++++++++++++++++++
     816 RBM3D/Chain/NewKLKGen.lean
$ grep -rln "Chain.NewKLKGen" RBM3D RBM3D.lean; grep "^import" RBM3D/Chain/NewKLKGen.lean | tr "\n" ";"
importers: none (grep exit 1)
import RBM3D.Induction.NewKLK;import RBM3D.Chain.Step2Gen;import RBM3D.BA.FlowPins;
$ touch RBM3D/Chain/NewKLKGen.lean; lake build RBM3D.Chain.NewKLKGen 2>&1 | tail -1
Build completed successfully (3744 jobs).
$ lake env lean scratchpad/T2405/g1.lean   # G1 examples (STNewKLK, stNewKLKAt_holds, stK2decay_holds) + #print axioms of the new public declarations
exit 0
[propext, Classical.choice, Quot.sound] : stNewKLKAtgL'_of, stNewKLKAtgL'_holds, stNewKLKgL'_of, stNewKLKAtgL_of_primed, stNewKLKgL_of_primed, newKLKGenHyp_band, STNewKLKAtgL', STNewKLKgL', NewKLKGenHyp
$ lake env lean scratchpad/T2405/precheck.lean   # import RBM3D; import RBM3D.Chain.NewKLKGen; #assert_rbm_axioms
exit 0; axiom audit: 11341 theorems, 3416 definitions, 0 axioms in `RBM` (compiler-generated declarations ex
$ lake env lean docs/tickets/checks/T2405-check.lean; grep -c error
exit 0; error lines: 0
$ python3 -I scratchpad/T2405/stmt.py stmt inst   # pins, hypothesis bundle, targets, then the compiled nonempty instances (statements; proofs in the file)
-- lines 55-66, 69-70, 378-407, 412-414, 617-619, 624-626, 634-638, 644-647, 664-665, 746-746, 750-750, 760-760, 775-782, 810-811
def STNewKLKAtgL' (d : ℕ) (κ 𝔡 C δ₀ : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →
    0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg (mk sz (fun _ => E)) n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOpg (mk sz (fun _ => E)) n u σ (STLKMg (mk sz (fun _ => E)) n u H σ) a‖ ≤
            C / (1 - u) * STJhatMg (mk sz (fun _ => E)) n D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKMg (mk sz (fun _ => E)) n u H σ a‖ ≤
            C / (1 - u) * (STJhatMg (mk sz (fun _ => E)) n D ℓ u H +
              STJhatMg (mk sz (fun _ => E)) n D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)
def STNewKLKgL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAtgL' d κ 𝔡 C δ₀ mk
def NewKLKGenHyp (d : ℕ) (κ 𝔡 : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∃ K_c C_K : ℝ, 0 ≤ K_c ∧ 0 ≤ C_K ∧
  (∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im →
      (∀ x y, (mk sz (fun _ => E)).S n x y ≠ 0 → zdistInf d (sz.L n) (x - y) ≤ 1) ∧
        (∀ x, ∑ y, ‖(mk sz (fun _ => E)).S n x y‖ ≤ 1) ∧
        (∀ x y, ‖(mk sz (fun _ => E)).S n x y‖ = ‖(mk sz (fun _ => E)).S n y x‖)) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → ‖(mk sz (fun _ => E)).m n‖ ≤ 1) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 → ∀ (σ : Fin 2 → Bool) (ℓ' D' : ℝ), 0 ≤ ℓ' → 0 ≤ D' →
      ∀ a a' : Zd d (sz.L n),
        ∑ b, ‖((mk sz (fun _ => E)).S n * Step2Gen_Theta ((mk sz (fun _ => E)).S n)
            ((u : ℂ) * (STmsigg (mk sz (fun _ => E)) n (σ 0) * STmsigg (mk sz (fun _ => E)) n (σ 1)))) a b‖ *
          tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (b - a') : ℕ) : ℝ) ≤
        K_c / (1 - u) *
          tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (a - a') : ℕ) : ℝ)) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 → ∀ σ : Fin 2 → Bool,
      (∀ a₁ : Zd d (sz.L n), ∑ x, ‖(mk sz (fun _ => E)).K n u σ ![x, a₁]‖ ≤
        C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)) ∧
      (∀ a₀ : Zd d (sz.L n), ∑ y, ‖(mk sz (fun _ => E)).K n u σ ![a₀, y]‖ ≤
        C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹))) ∧
  (∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      κ ≤ ((mk sz (fun _ => E)).m n).im → 0 ≤ u → u < 1 →
      ∃ ζ : ℂ, ζ.im = (1 - u) * ((mk sz (fun _ => E)).m n).im ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
          (a : Fin 2 → Zd d (sz.L n)), (mk sz (fun _ => E)).LM n u H σ a = loopFine d (sz.L n) (sz.W n) H ζ σ a) ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (x : Idx d (sz.L n) (sz.W n)),
          (mk sz (fun _ => E)).GMM n u H x x = Gres H ζ true x x - (mk sz (fun _ => E)).m n))
theorem stNewKLKAtgL'_of (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ)
    (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) (hyp : NewKLKGenHyp d κ 𝔡 mk) :
    ∃ C : ℝ, 0 < C ∧ STNewKLKAtgL' d κ 𝔡 C (κ / 2) mk := by
theorem stNewKLKAtgL'_holds (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ)
    (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) (hyp : NewKLKGenHyp d κ 𝔡 mk) :
    STNewKLKAtgL' d κ 𝔡 (stNewKLKAtgL'_of hd κ 𝔡 hκ mk hyp).choose (κ / 2) mk :=
theorem stNewKLKgL'_of (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz)
    (h : 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 mk) :
    STNewKLKgL' d mk := by
theorem stNewKLKAtgL_of_primed {κ 𝔡 C δ₀ : ℝ} {mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz}
    (h : STNewKLKAtgL' d (κ / 2) 𝔡 C δ₀ mk)
    (hdom : ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
      κ / 2 ≤ ((mk sz (fun _ => E)).m n).im) :
    STNewKLKAtgL d κ 𝔡 C δ₀ mk :=
theorem stNewKLKgL_of_primed {mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz} (h : STNewKLKgL' d mk)
    (hdom : ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      |E| ≤ 2 - κ → κ / 2 ≤ ((mk sz (fun _ => E)).m n).im) :
    STNewKLKgL d mk := by
theorem newKLKGenHyp_band (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    NewKLKGenHyp d κ 𝔡 (fun sz E => bandStep2Mat sz E) := by
example : STNewKLKgL' 3 (fun sz E => bandStep2Mat sz E) :=
example : ∃ C : ℝ, 0 < C ∧ STNewKLKAtgL' 3 (1 / 10) (1 / 10) C (1 / 20) (fun sz E => bandStep2Mat sz E) := by
example (d : ℕ) : STNewKLK d :=
example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
    ‖STthetaOpg NewKLKGen_cm0 0 (1 / 32) σ (STLKMg NewKLKGen_cm0 0 (1 / 32) NewKLKGen_H0 σ) a‖ ≤
        C / (1 - 1 / 32) * STJhatMg NewKLKGen_cm0 0 1 2 (1 / 32) NewKLKGen_H0 *
          STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) ∧
      ‖STELKLKMg NewKLKGen_cm0 0 (1 / 32) NewKLKGen_H0 σ a‖ ≤
        C / (1 - 1 / 32) * (STJhatMg NewKLKGen_cm0 0 1 2 (1 / 32) NewKLKGen_H0 +
          STJhatMg NewKLKGen_cm0 0 1 2 (1 / 32) NewKLKGen_H0 ^ 2 * (if 1 ≤ (2 : ℝ) then 1 else 0)) *
          STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) := by
example (κ 𝔡 : ℝ) (hκ : 0 < κ) (hyp : NewKLKGenHyp 3 κ 𝔡 (fun sz E => NewKLKGen_baMk sz E)) :
    ∃ C : ℝ, 0 < C ∧ STNewKLKAtgL' 3 κ 𝔡 C (κ / 2) (fun sz E => NewKLKGen_baMk sz E) :=
$ name clash: hits of each new public name outside the new file (grep -rn -F over RBM3D, RBM3D.lean); sorry/admit/native_decide/axiom in the new file
STNewKLKAtgL':0 STNewKLKgL':0 NewKLKGenHyp:0 stNewKLKAtgL'_of:0 stNewKLKAtgL'_holds:0 stNewKLKgL'_of:0 stNewKLKAtgL_of_primed:0 stNewKLKgL_of_primed:0 newKLKGenHyp_band:0 NewKLKGen_:0 
0
ports: none (no RBM1D/RBM2D text); copies of RBM3D Induction/NewKLK.lean, last commit b06ff9b
```

Narrative (facts from the file and the tool log):
- Proof: `stNewKLKAtgL'_of` is `nkl_at` (`NewKLK.lean:993`) with `S`, `Θ`, `m`, `K`, `LM`, `GMM` read from `mk`; `nkl_conv_two`, `nkl_bound2`, `nkl_ward_LKM` are copied over a generic kernel/family (`NewKLKGen_conv_two`, `_bound2`, `_ward_LKM`); `nkl_conv_P` is replaced by the hypothesis F7. `C = 2K_c + 2C_s(4+C_K) + C_sC_T`.
- Opened privates (18, `open private … from RBM3D.Induction.NewKLK`, precedent `DuhamelII.lean:42`; each is referenced in the file): generic proof `nkl_Cs_ge_one`, `nkl_tailT_shift`, `nkl_tailT_le_tailW`, `nkl_tailW_eq_of_near`, `nkl_tailW_far`, `nkl_zdistInf_sub_comm`, `nkl_zdistInf_tri`, `nkl_dist_cases`, `nkl_ward_L`, `nkl_gres_blockMat_true`; band discharge and instances `nkl_SB_support`, `nkl_theta_tail`, `nkl_SBTheta_tail`, `nkl_SBTheta_row`, `nkl_conv_P`, `nkl_ward_K`, `nkl_mE_zero`, `nkl_STGMM_zero`. Copying them instead costs their spans ((a′) C5 (iv): 173 + 219 lines).
- Final shape differs from (a′) C3 in two places: `K_c, C_K` are `∃` inside `NewKLKGenHyp` (equivalent to taking them as arguments), and F9 is stated for `σ : Fin 2 → Bool` (the only length used). Target 1 concludes `∃ C > 0, STNewKLKAtgL' … (κ/2)`; `stNewKLKAtgL'_holds` is its pointwise form at the chosen `C`.
- Registry: the pre-check on commit 5204384 (first version) failed with `[RBM.BA.NewKLKGenHyp, RBM.BA.STNewKLKAtgL']` unclassified (tool log). Fixed inside the sole writable file by the public theorems `newKLKGenHyp_band` and `stNewKLKAtgL'_holds` (conclusion head = the premise, as `stNewKLKAt_holds`); `Test/Axioms.lean` is not edited. The scan now counts both as proved, although at BA they remain owed (T3-BA); see (d).
- `rfl` analysis of (a′) C3, as met: Fail 2 confirmed (diagonal `GMM` at the band needs `unfold STGMM; simp; rfl`); Fail 4 handled (`change` unfolds `STLKMg`/`STLMg` in the generic Ward step); the `LM` clause of F9 is `rfl`; `Step2Gen_Theta (SB ..) ξ` against `Theta ..` and `STmsigg` against `mSigma` are accepted by `exact` (defeq), no `unfold`; Fail 3 avoided (`hE2` is stated on `mE E`); Fail 1 not attempted: the unprimed band pin comes from `stNewKLKgL_of_primed` (κ' = κ/2, `Ind.half_le_mE_im`) and `bandStep2_STNewKLK`, composed in the `example` for every `d`.
- Instances (`d = 3`): the band family satisfies F5-F9 for every `κ, 𝔡 > 0`; pointwise instance at `sz0` (`sz0_values`, `Defs/Sizes.lean:267`: `L = 4`, `W = 32`, `lam = 1/64`), `n = 0`, `E = 0`, `u = 1/32`, `D = 1`, `ℓ = 2` (indicator on), `H = 0`, `‖G_u-M‖ ≤ u/(1-u) = 1/31 ≤ 1/20` (`nkl_STGMM_zero`, `NewKLK.lean:1231`); BA statement-level `example` over a private `Step2Mat` on `baFM sz sz.lam E`, hypothesis `NewKLKGenHyp` left open.
- G1: `NewKLK.lean` and `Step2K2.lean` are untouched; the three G1 `example`s and the check file compile (exit 0 above).

## (c) Verified Mathlib names (`#check` in the build environment)
`NeZero.one_le`, `mul_le_of_le_one_left`, `Finset.le_sup'`, `Real.sqrt_pos`, `half_pos`, `Complex.abs_im_le_norm`, `Matrix.IsHermitian.submatrix`, `Exists.choose_spec`, `Matrix.isHermitian_zero`, `div_le_iff₀`, `div_le_div_of_nonneg_right`, `Complex.norm_natCast`. Deprecated, not used: `mul_le_one₀` (warning seen), `if_true` (replaced by `simp`).

## (d) Open issues and paper-delta candidates
- T2405a, T2405b: as in (a′) C6. T2405c: the generic theorems are conditional adapters (CLAUDE.md §5.6), not the paper's `lem:newKLK`; the BA instance of `NewKLKGenHyp` (F5-F9 at BA) is owed to T3-BA and proved nowhere here. T2405d: the unprimed corollary route gives `δ₀ = κ/4` (merged `stNewKLK_holds`: `κ/2`), allowed by `∃ C δ₀`.
- Registry (dispatcher): `NewKLKGenHyp` and `STNewKLKAtgL'` pass the scan only through the band theorems; the dispatcher may register them in `owedProps` with owner T3-BA, since `Test/Axioms.lean` is not a writable file of this ticket.
- Not done here: BA proofs of F5-F9, `STK2decaygL` at BA (T3-BA), the root import `import RBM3D.Chain.NewKLKGen` (hub, after the last `import` line of `RBM3D.lean`).
