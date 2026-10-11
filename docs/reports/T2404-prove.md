Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 02:37:29 UTC 2026

Notation (d ≥ 3): `N=(WL)^d`, `w=W^{-d}`, `P_D(x)=STprof=W^{-d}𝒯̃^ℓ_{t,D}(x)` (`Step2Defs.lean:75`, `P_D ≥ w·W^{-D}`), `ℓ_t=ellT`, `Y=y^5`, `y=N^{τ/10}`. Targets: (1) `STEMn2PolygL`, (2) `STEMn2ExpgL`, (5′) the `J` form. The matrix-level lemmas (3) are unchanged. All proofs read below are the band proofs (`EMn2Poly.lean:838`, `EMn2Exp2.lean:884`, `EMn2Exp1.lean:1206,1465`); a row is carrier-clean if it uses only `C.K, C.L, C.S, C.eta` and `sz`.

### (i) Exponent / constant table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `τ` budget, Poly (`EMn2Poly:857-862`); far3 uses the same `y` (row 2) | LW event at level `τ/5` (`y²=N^{τ/5}`), `Y=y⁵=N^{τ/2}`, loss `Y²=N^τ` | `2·3^d K² ≤ N^{τ/2}`, `K=max(C₁3^{C₂}, c⁻¹)` (`psi_cmp` `:752`, class constants) | `N^{τ/2}/(2·3^dK²) → ∞` (`SizeTendsto`) |
| 2 | far sum `S̃₃` assembly (`EMn2Exp2:818,944`) | `A1=3^d√(1+cB⁻¹)`, `A2=4·3^d·2^{d-2}e·(C_I+C_R)`, `Y=N^{τ/2}` | `2(A1+A2+1) ≤ Y`; then `A1Y+A2 ≤ Y²` | `N^{τ/2}/(2(A1+A2+1)) → ∞` |
| 3 | size data `cB` (`Step2Iterate:1049-1051`) | `cB=(𝔡⁻²+1)⁻¹`; from `Bctl=W^{-d}B_{u,0}`, `B_{u,0} ≥ (g²+1-u)⁻¹ ≥ (g²+1)⁻¹`, `g ≤ 𝔡⁻¹` (`WO`) | `cB·w ≤ Bctl` for all `u∈[0,1)`; model-free given `WO` | `(g²+1)⁻¹ ≥ cB`, equality iff `g=𝔡⁻¹` |
| 4 | `w³ ≤ Bctl^{1/2}` (`EMn2Exp2:804`) | `(w³)² = w·w⁵ ≤ w·cB ≤ Bctl`, uses `w⁵ ≤ cB` i.e. `W^{5d} ≥ cB⁻¹` | proof takes `W ≥ max(1,cB⁻¹)` (`EMn2Exp2:949`ff): `w ≤ cB`, `w ≤ 1`, so `w⁵ ≤ w ≤ cB` | the route loses `W^{-4d}` (true need `W^{5d} ≥ cB⁻¹`) |
| 5 | upper size data `Bctl ≤ N^{-c}` (near case, `EMn2Exp1:1206`ff) | `c=min(2𝔡𝔠,ε)/2`; `Bctl ≤ g⁻²W^{-d}+ (N(1-t))⁻¹ ≤ W^{-2𝔡}+N^{-ε/2}` from `WO`, `Bandwidth`, `RangeCond ε/2` | `1-t ≥ N^{-1+ε/2}` | `N^{ε/2}`-factor |
| 6 | near-case exponent `ε'` (`EMn2Exp1`, near proof) | `ε'=min(ε₀, d·c/4, d/2)` | `ε' ≤ ε₀` (to use `W^{-ε₀} ≤ W^{-ε'}`), `ε' ≤ d/2` (`emn2Exp_psiClass`) | instance: `ε'=1/80 ≤ 1/20 ≤ 3/2` |
| 7 | cutoff scales | `ℓ*=(log W)^{3/2}ℓ_t`, `ℓ†=(log W)^{7/4}ℓ_t` | `ℓ*≤ℓ†` iff `log W ≥ 1`; gap `2(ℓ*+1) ≤ ℓ†` iff `(log W)^{1/4} ≥ 4`, i.e. `log W ≥ 256` (`EMn2Exp1:258`) | at `log W=256`: `ℓ*=4096, ℓ†=16384`, `2(ℓ*+1)=8194` (factor 2) |
| 8 | shift loss `K_n`, `K₁` | `K_n=2^{d-2}e^{2(log W)^{3/4}}`, `K₁=2^{d-2}e` | `K_n ≤ N^{δ}` eventually: `(log W)^{3/4} = o(log N)` as `W ≤ N` | `o(log N)` |
| 9 | near-case conversion (`emn2Exp_ev_exp_pow`, `a=7/8`) | `C e^{2(log W)^{7/8}} ≤ N^{τ/2}`, `C=4√(1+cB⁻¹)` | eventually, any `τ>0` | asymptotic only (script (c)) |
| 10 | **(HK)** 2-loop far kernel (replaces `emn2Exp2_STKloop_two`, `norm_STKloop` `:717,:728`) | `∀D>0, ∀ᶠn, ∀x,x', ℓ*_{t_n} ≤ |x-x'|_∞ → ‖C.K n t_n ![s,!s] ![x,x']‖ ≤ W^{-(2d+D)}` (`s` any; only `u=t_n`, `s=0` is read: `EMn2Exp2:1025`) | band: `‖K‖=w‖Θ‖`, `‖Θ‖ ≤ W^{-(D+d)}` (`kellStarEv`, `δ=1`); then `‖K‖ ≤ w·P_D` since `P_D ≥ w W^{-D}` | none in (HK) (exact); asymptotic margin below |
| 11 | BA source of (HK) | `K^{(2)}_{(σ,σ')}=W^{-d}(Θ·M^{(σσ')})_{a₁a₂}` (`BA/KSolve.lean:66`), `Θ ≤ C·B_{u,r}e^{-c r/ℓ_t}` (`Prop5Decay`, `Propagator/Pins.lean:34`), `|M_{ab}| ≤ (Cg)^{|a-b|}` or `c⁻¹e^{-c|a-b|}` (`7_8:1891-1904`) | need `c(log W)^{3/2} ≥ log(2C')+(1-τ)log N+(D+d+1)log W` (`B ≤ 2(1-u)⁻¹ ≤ 2N^{1-τ}`) | `(log W)^{1/2}`-growth; thresholds in script (b) |
| 12 | `η` | `η=(1-t)Im m`; need `0<η ≤ 1-t` | band `Im m ≤ 1`; BA `|m| ≤ 1` (Ward, `7_8:1909-1910`), `Im m ≥ κ>0` (`BAdom`) | `1-Im m ≥ 0`; only `η ≤ C(1-t)` is needed (absorbed in `A2`) |
| 13 | `RangeCond τ`, `τ=ε/2`, `t<1` | band: merged. BA: `BAt0=Im m/(Im m+Im z)` (`MFixedPoint:279`), `1-t₀=Im z/(Im m+Im z) ≥ Im z/2 ≥ N^{-1+ε}/2` (`BAdom`: `Im z ≥ N^{-1+ε}`, `Im z ≤ 1`, `Im m ≤ 1`) | `N^{-1+ε}/2 ≥ N^{-1+ε/2}` iff `N^{ε/2} ≥ 2` | `N^{ε/2}/2` |
| 14 | kernel `S` of the carrier (`Carrier.lean:64`, `FlowFM`) | `|S_{cc'}| ≤ 1`, `S_{cc'}=0` for `|c-c'|_∞>1`, ≤`3^d` partners (`EMn2Poly:466,474`) | band `SB`; BA `S=1` (`FlowPins:327`): satisfies both | partners `1 ≤ 3^d` |
| 15 | Hermitian realization of the loops | `C.L n u σ a ω = loopFine d L W H z σ a`, `H` Hermitian, `Im z=C.eta n u>0`, `z=E+(1-u)m` | needed by the HS/Cauchy-Schwarz lemmas (class R) | BA: `BALloop=loopFine(seqHflowBA)(ztOf …)` (`FlowPins:264`), `Im ztOf=(1-t)Im m=etaOf`; Hermiticity of `seqHflowBA` **not checked here** |
| 16 | (TTT2) and radial sum | `C_I(d), C_R(d)` model-free; call at `u=t`: needs `0<g=sz.lam n`, `t<1`, disjunction `g²/L² ≤ 1-t ∨ 1-t ≤ g²/L²` (trivial by `le_total`) | `0<sz.lam n` from `WO` (`W^{-d/2+𝔡} ≤ lam`) | BA keeps the real `sz.lam`; `withLam 0` enters only the law `μ` (`FlowPins:398`) |
| 17 | **5′ `J` form** (`7_8:1999`: `Ĵ ≺ J`, `J ≥ W^{-d}` deterministic) | extra event `Ĵ ≤ N^{τ'}J`, `τ'=τ/10`; `(Ĵ+w)³ ≤ N^{3τ'}(J+w)³`; `A2 → A2·N^{3τ'}` in row 2 | `3τ' < τ/2` | slack exponent `τ/5` (script (c)); `J ≥ W^{-d}` not used, only `J ≥ 0` and `w³ ≤ Bctl^{1/2}` |

Consequences: (a) the far-sum proof (`emn2Exp_far3`) reads `K` only through (HK) (rows 10-11) and `L-K` only through `Ĵ` (`STJhatg`); the first estimate does not read `K`. (b) rows 12, 13, 5, 3 are elementary at BA from `BAdom`, `Admissible`, `|m| ≤ 1`. (c) the first estimate and the near case (`EMn2Exp1:1206`ff, first estimate at the truncated profile `emn2ExpPsi`) read the model only through rows 12, 14, 15 and `STInitialGT2gL.1` (`‖G-M‖_max ≺ W^{-ε₀}`, row 6); `far12` was read here only through its header (no `Ĵ`, no `(GijGEX)`). (d) Row 11 note: BA `Θ` carries the coupling `g₀=√t₀·g ≤ g`; `ℓ_t` is nondecreasing in `g`, so decay at scale `ℓ_t(g₀)` gives (HK) beyond `ℓ*(g)` (the BA owner discharges this).

### (ii) One concrete instance and numerical checks

Instance: `d=3`, `sz0` (`L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^{-6}`, `Defs/Sizes.lean:260`), `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z_n=1/2+iN^{-4/5}` (`Induction/Defs.lean:413`), `t≡1/16`, `ε₀=1/20`, `Ψ=W^{-1}`, `ℓ=ℓ†` (inside `[0,(log W)^{10}ℓ_t]`; `ℓ=2ℓ*` would put the midpoint of `Reg` outside `(ℓ*,ℓ]` for `(log W)^{1/4}>4`), `D=1`. The Lean examples are sequence-level (`∀ᶠ n`); the non-asymptotic hypotheses hold for every `n`, the eventual ones from the thresholds printed. `lemT` is printed as a float (`≈1`); the check is `lemT ≥ 1/16`, computed from `msc z` at 80 digits.
```
$ python3 scratchpad/T2404/inst.py     # (a) all deterministic hypotheses at n_gap, 1e30, 1e60; (b) (HK) margin thresholds
{'n': 8606914282433837939747, 'L': 34427657129735351758992, 'logW': 256.0, 'logN': 923.6794415416798, 'ell_t': 1.0, 'ell_star': 4096.0, 'ell_dag': 16384.0, 'Lhalf': 1.7213828564867676e+22, 'lemT': 1.0
  all True: True []
{'n': 1000000000000000000000000000000, 'L': 4000000000000000000000000000004, 'logW': 348.8534998519066, 'logN': 1257.9520410085436, 'ell_t': 1.0, 'ell_star': 6515.753208514206, 'ell_dag': 28159.529725
  all True: True []
{'n': 1000000000000000000000000000000000000000000000000000000000000, 'L': 4000000000000000000000000000000000000000000000000000000000004, 'logW': 694.2412638010135, 'logN': 2501.3479912253283, 'ell_t':
  all True: True []
n_gap (logW>=256) =~ 8.607e+21
c=1: Kfar margin>=0 first at n~8.159e+5 (logW=71.5)
c=0.5: Kfar margin>=0 first at n~2.431e+24 (logW=284.2)
c=0.1: Kfar margin>=0 first at n~3.567e+615 (logW=7090.3)
```
`inst.py` checks at each `n`: `L≥3`, `WO`, `Bandwidth`, `locDomain`, `1/16 ≤ lemT(z_n)`, `Ψ` window, `ℓ ≤ (log W)^{10}ℓ_t`, `(log W)^{1/4} ≥ 4 ⇒ 2(ℓ*+1) ≤ ℓ†`, far window `ℓ† < ⌊L/2⌋`, `Reg` nonempty (midpoint `c` of `a,b` with `|a-b|=⌊ℓ†⌋+1`: `ℓ* < |c-a|,|c-b| ≤ ℓ`); every line prints `all True`. External hypothesis (HK), limit computation (TEAM §8 lesson 14): the margin `c(log W)^{3/2} − log 2 − (1-τ)log N − (D+d+1)log W ≥ 0` (`τ=ε/2=1/20`, `D=1`) is the three `c=` lines: it holds eventually for every fixed `c>0` because `(log W)^{3/2}` beats the linear terms (`log N ≤ log W/𝔠` by `Bandwidth`); the threshold in `log W` grows like `c^{-2}` (`c=1`: `log W=71.5`; `c=1/2`: `284.2`; `c=1/10`: `7090.3`).
```
$ python3 scratchpad/T2404/inst2.py     # (c) rows 3, 5, 6, 9 at sz0
cB=0.00990099 c=0.0166667 eps'=0.0125 (<=eps0=0.05)
n=1.0e+6 {'cB_ok': True, 'Bctl_le_N_minus_c': True, 'W_ge_1_over_cB': True}
n=1.0e+30 {'cB_ok': True, 'Bctl_le_N_minus_c': True, 'W_ge_1_over_cB': True}
tau=1.0: near-case conversion exp(2 logW^(7/8))*const <= N^(tau/2) first at n~2.204
tau=0.01: near-case conversion exp(2 logW^(7/8))*const <= N^(tau/2) first at n~7.75e+43429447
```
Row 9 is the only astronomically large threshold (`τ=0.01`: `n≈7.75e43429447`); it is the asymptotic `∀τ>0, ∀ᶠ n` of `Prec`, not a restriction on the instance, and the Lean examples keep it at the sequence level.
```
$ python3 scratchpad/T2404/e.py     # (d) rows 1, 4, 17: exponent arithmetic (exact fractions)
tau 1/100 | Poly/Exp: y^2=N^1/500 (LW event at tau/5 OK), Y=y^5=N^1/200, Y^2=N^1/100=N^tau | J-form (A2 -> A2 N^3/1000 in hY: Y>=2(A1+A2 N^3/1000+1)): needs 3/1000<1/200: True; slack exponent 1/500
tau 1/20 | Poly/Exp: y^2=N^1/100 (LW event at tau/5 OK), Y=y^5=N^1/40, Y^2=N^1/20=N^tau | J-form (A2 -> A2 N^3/200 in hY: Y>=2(A1+A2 N^3/200+1)): needs 3/200<1/40: True; slack exponent 1/100
tau 1 | Poly/Exp: y^2=N^1/5 (LW event at tau/5 OK), Y=y^5=N^1/2, Y^2=N^1=N^tau | J-form (A2 -> A2 N^3/10 in hY: Y>=2(A1+A2 N^3/10+1)): needs 3/10<1/2: True; slack exponent 1/5
w^3=W^-9, (W^-d)^5=W^-15 <= c_B eventually (W>=1/c_B); w^6=W^-18 <= Bctl>=c_B W^-d slack exponent in log_W: -15 (<=0 ok)
```

### Verdicts
- Target 1 (`STEMn2PolygL`): PASS. Hypotheses: rows 1, 12, 14, 15 and the class constants; `STInitialGT2gL` and the `Ψ` window are not used by the proof (`EMn2Poly` header).
- Target 2 (`STEMn2ExpgL`, `3 ≤ d`): PASS. Extra hypotheses: rows 3-9, 10 (HK, owed by BA row 11), 13, 16, and `STInitialGT2gL.1` in the near case (row 6); `ekPropTInf_holds` and `emn2Exp2_exists_CR` are model-free.
- Target 5′ (`J` form): PASS mathematically (row 17: any deterministic `J ≥ 0` with `Ĵ ≺ J`, also pointwise `Ĵ ≤ J`; slack exponent `τ/5`); the Lean line count is not assessed here.
- Open for BA (not blocking): row 15 Hermiticity of `seqHflowBA` unverified here; row 11 is the `(Kn2sol)` + `Prop5Decay` + `Mbound` composition (`7_8:2002` "obtain `eq:kn2sol_decay`"), not yet a merged BA theorem.

## (a′) Preflight corrections — Sun Oct 11 02:58:33 UTC 2026

Repair of the 1a-audit RETURN (`docs/reports/T2404-1a-audit.md`, 02:39:42 UTC). Section (a) is unchanged (the audit reran its numerics: they reproduce); this section adds the design-gate deliverables (i)-(iv), replaces the `Prop5Decay` source of row 11, and states row 15. Statements are in mathematics (no Lean written); every proposed name has 0 hits in `RBM3D/` and `docs/tickets/checks/`. T2405: `git log main..t/T2405` is empty and `docs/reports/T2405-prove.md` does not exist, so the coupling clause is vacuous now; (HK) is one named hypothesis T2405 can reuse.

### (a′-i) Hypothesis table. Generic form is over `C = mk sz z : FlowFM sz` (fields `L K S eta m`, `Chain/Carrier.lean:55`); `Hf, ζf` are explicit parameters (below).
| # | band fact (file:line) | generic form | BA source | C1 |
|---|---|---|---|---|
| H1 | `etaT_pos`, `sz.seqHflow_isHermitian`, `etaT_eq_zt_im`, `Lloop = loopFine (seqHflow)(zt)` (`EMn2Poly:848-849,886-888`; `EMn2Exp1:1232`; `EMn2Exp2:916`) | (R): for `0≤t≤T0`, all `n,ω`: `Hf sz z t n ω` Hermitian, `0 < Im ζf = C.eta n (t n)`, `C.L n (t n) σ a ω = loopFine (Hf) (ζf) σ a` (all `k`) | `BALloop = loopFine (seqHflowBA lam0 n u ω)(ztOf m E t)` (`FlowPins:264`), `Im ztOf = etaOf` (`GLoopFlow:55,58`). Hermitian of `seqHflowBA`: private copies `FlowPins:925`, `Step1Trivial:104`, `ConArg:310` | clean; **row 15**: public Hermitian lemma (the private proof is `FlowPins:925-930`) owed by the BA twin of T2 |
| H2 | `η ≤ 1-t` via `norm_mE` (`Defs/Semicircle:63`) (`EMn2Exp2:920-923`) | (E): `C.eta n (t n) ≤ 1 - t n` | `Im m ≤ ‖m‖ ≤ 1` (`BAm_norm_le_one`, `BA/Ward:136`), `etaOf = (1-t) Im m` | clean |
| H3 | `norm_SB_le_one`, `SB_eq_zero_of_far` (`EMn2Poly:466,474`) inside `emn2_ee_le` (`:679`, takes any real `g`) | (S): `∀ n ∃ g, C.S n = SB d (sz.L n) g`; matrix-level lemmas unchanged | `baFM.S = 1` (`FlowPins:322`): needs `SB d L 0 = 1` (`sbKernel d L 0 = 1_{x=0}`, `Defs/Block:38`), not merged: owed by the BA twin | clean; 1 small lemma owed |
| H4 | `hflow.1` = `Admissible` (`EMn2Poly:842`; `EMn2Exp1:1226-1229`; `EMn2Exp2:906-910`) | (A): `Flow … → sz.Admissible 𝔠 𝔡` (T8 field `flowOK_adm`) | `BAFlow.1` (`FlowPins:389`) | clean |
| H5 | `t<1` via `v3_premises_of_stFlow` (`Green/Pins:1049`) (`EMn2Exp2:913`) | (T): `∀ n, T0 sz z n < 1` (T8 field `flowOK_T`) | `BAt0_lt_one` (`BA/MFixedPoint:285`), `Im z>0` from `BAdom` | clean |
| H6 | `ST_Bdata_holds` (`Step2Iterate:1049`; read at `EMn2Exp1:1237,1495`, `EMn2Exp2:928`) | (B): `∃ cB c>0, ∀ᶠ n, ∀ u∈[0,t n], cB W^{-d} ≤ Bctl n u ≤ N^{-c}` (hypothesis; `STBdata` form, `Step2Events:209`) | only `WO`, `Bandwidth`, `1-t ≥ N^{-1+ε/2}` (row 13 of (a)); small, owed by the BA twin | clean |
| H7 | `emn2Exp2_STKloop_two` (`:717`, `KLK_two`), `emn2Exp2_norm_STKloop` (`:728`), `emn2Exp_kellStar_far` (`EMn2Exp1:1637`) | **(HK)** one inequality hypothesis (below) | see “Row 11” | blocker only if the BA owner fails to supply it |
| H8 | `ekPropTInf_holds` (`PropTInf:534`, read `EMn2Exp2:942`) | **reused unchanged** at `(L,g,u,t) = (sz.L n, sz.lam n, t n, t n)`: the real `sz.lam`, as in `STprof` (`Step2Defs:75`); needs `0<sz.lam n` (`WO`) | same (BA keeps the real `sz.lam`; `withLam 0` only in the law) | clean |
| H9 | `emn2Exp2_exists_CR` (`:314`, private, used by `DuhamelII:42`) | reused, name and type kept | — | clean |
| H10 | `kellStarEv` (`Path/KellStar:173`), `emn2Exp_kellStar_far` | **not read generically**; only the band proof of (HK) (`stEMn2Exp_holds` corollary) | — | n/a |
| H11 | `STInitialGT2.1` (`EMn2Exp1:1272`), `STLWassm`, `STLWassmExp` | statement hypotheses `STInitialGT2gL`, `STLWassmgL`, `STLWassmExpgL` (`Carrier:140`, `Step2Gen:265,62`) | other gates' pins: hypotheses of the examples | clean |
| H12 | `ST_W_tendsto :235`, `ST_prof_le_Bctl :272`, `ST_STprof_pos :165`, `ST_size_pow_big :487` (`Step2Events`), `STBctl_pos` (`ScaleFacts:64`) | reused unchanged (they read only `sz`) | — | clean |
| H13 | `ST_prec_mono_eventually :49`, `ST_prec_sup :76` (`Prec sz` only) | private `PrecL` copies, stems `emn2Exp_` (about 27 lines); the `StochDomAt` calculus (`Defs/StochDomAt:325-470`) takes any measure, no hypothesis on `law sz` | — | clean |
| H14 | `ST_JhatM_nonneg :699`, `emn2Exp2_STLKM_le :738` (matrix-level `Ĵ`) | private lemmas from the definition of `STJhatg` (`Step2Gen:56`) (about 14 lines) | — | clean |
`T1` owns `Step2Iterate`: of its declarations the three files read only `ST_Bdata_holds` (grep of every name of `Step2Iterate`, `Step2Events`, `Step2Scale`, `Step2K2`, `Step2Core`, `ScaleFacts`: the rest of the list is H12-H14). `kellStarEv` / `ekPropTInf_holds` / `emn2Exp2_exists_CR` are model-free or band-only as marked.

**Row 11 (replaces the `Prop5Decay` citation; row 15 above).** `Prop5Decay` needs `‖m‖=1` (`Propagator/Pins:34`) and is dropped. The G3b Θ-bound `baTheta_weighted_l1` (`BA/GreenStab:251`) is stated for `BATheta … σ σ` (same sign, gapped, from `baProp5s_of_real`, `Prop5Short:608`); (HK) reads the mixed pair `(s,-s)`, i.e. `K^{(2)}_{(s,-s)} = W^{-d}(Θ^{(s,-s)} M^{(s,-s)})` (`BAKsolve`, `KSolve:58-66`). So the sources are: Θ: `baProp5_holds` (`BA/Prop6Path:850`; pin `BAProp5`, `FlowPins:173`; `BAReal` data, `|Θ(0,a)| ≤ C B_{t,|a|} e^{-c|a|/ℓ_t(g₀)}`) with the shift `baP8_BATheta_shift` (`Prop6Path:497`); M: `BAMss_norm_eq_BAK` (`KKernel:102`, `‖M^{(σσ')}_{ab}‖ = BAK_{ab} = |M_{ab}|²`), `BAK_row_sum` (`:124`, row sum 1), `BAMB_decay_large` (`CombesThomas:509`) and G3b `baM_row_l1`, `baM_col_l1`, `baM_rhohat` (`GreenStab:116,123,147`, weighted `ℓ¹` row of `M`); identification of `BAKloop = BAKsol` (`FlowPins:283`, `if … then h.choose`) with the `(Kn2sol)` solution: `baK_unique` (`KSolve:568`) + `BAKsolve`. The composition `(ΘM)(x,x')` is **not a merged theorem**: it is owed by the BA twin row of T2. `ℓ_t` is nondecreasing in `g` (`ellT = min(max(g/√|1-t|,1),L)`, `Defs/Params:32`), `g₀ ≤ g`, so decay at `ℓ_t(g₀)` gives decay beyond `ℓ*_t(g)`. Limit check for this route (split `|x-x'| ≤ |x-c|+|c-x'|`; A: `|x-c| ≥ r/2`, rate `c₅/2`, prefactor `2C₅/(1-t)`; B: `|c-x'| ≥ r/2`, rate `c₀`, the extra volume `L^d ≤ N`; `1-t ≥ N^{-1+ε/2}`, `N^𝔠 ≤ W`; `C₅=10`, `d=3`, `D=1`, `τ=1/20`; sz0 of (a)):
```
$ cd scratchpad/T2404 && python3 hk2.py
rate=1  A: n~3.94e+4 (logW=56.4) | B: n~2.277e+10 (logW=122.7)
rate=0.5  A: n~8.778e+18 (logW=221.6) | B: n~1.006e+42 (logW=487.0)
rate=0.1  A: n~1.069e+478 (logW=5507.0) | B: n~4.246e+1054 (logW=12145.3)
at n=1e60: marginA(rate1)=13135.9 marginB(rate1)=10634.6 marginA(rate.1)=-3327.0 marginB(rate.1)=-5828.4
```
At `n=1e60` both margins are positive for rate 1 and negative for rate 0.1; the thresholds in `log W` grow like `rate^{-2}` (A/B: rate 1: `56`/`123`; rate 0.5: `222`/`487`; rate 0.1: `5507`/`12145`). (HK) is an eventual (`∀ᶠ n`) hypothesis; the rates `c₅, c₀` are BA constants (`BAp5s_rate`, `BAct_rate`), so no threshold is asserted for the instance beyond these rows.

### (a′-ii) Generic statements (names proposed; `Step2Gen:471` and `:483` are the targets' shapes)
Data of every generic statement: `d`, `law : ∀ sz, Measure sz.SeqΩ`, `Flow`, `mk : ∀ sz z, FlowFM sz`, `T0` (as `STEMn2PolygL`), plus the **realization** `Hf sz z t n ω ∈ Matrix (Idx d (sz.L n) (sz.W n))²` and `ζf sz z t n ∈ ℂ` (explicit parameters: no `Classical.choose`). Bundles (Props, one definition each):
- `emn2PolyFacts d Flow mk T0 Hf ζf` (`EMn2Poly`): for all `κ ε 𝔡 𝔠 sz z`, `0<κ, 0<ε, 0<𝔡`, `Flow sz κ ε 𝔠 𝔡 z`: (A) H4; (R) H1 for every `t` with `0 ≤ t ≤ T0`; (S) H3.
- `emn2ExpFacts` (`EMn2Exp1`) = `emn2PolyFacts` ∧ (T) H5 ∧ (E) H2 ∧ (B) H6.
- `emn2ExpHK d Flow mk T0` (`EMn2Exp2`) = **(HK)**: for the same `κ ε 𝔡 𝔠 sz z`, `0 ≤ t ≤ T0`: `∀ D>0, ∀ᶠ n, ∀ x x' s, ℓ*_{t n} ≤ |x-x'|_∞ → ‖C.K n (t n) ![s,!s] ![x,x']‖ ≤ W^{-d} · W^{-(D+d)}`, `ℓ*_u = emn2ExpEllStar sz n u = (log W)^{3/2} ellT (sz.L n) (sz.lam n) u` (`EMn2Exp1:172`).

**T1 `stEMn2PolygL_of`** (`EMn2Poly`): `∀ d law Flow mk T0 Hf ζf`, `emn2PolyFacts … → STEMn2PolygL d law Flow mk T0`. No `3 ≤ d` (as the pin). Conclusion = `Step2Gen:471` verbatim: `∀ κ ε 𝔡 >0, 𝔠 sz z, Flow → ∀ t, 0≤t≤T0 → ∀ ε₀>0, Ψ, STPsiClass → STInitialGT2gL (mk sz z)(law sz) t ε₀ Ψ₀ → STLWassmgL … t Ψ → PrecL (law sz) ‖STEEg (mk sz z) n (t n) k σ a ω‖ ≺ η⁻¹ Ψ₀ Ψ_{|a₁-a₂|}⁴`. Corollary `stEMn2Poly_holds d : STEMn2Poly d` (old name, old statement, `EMn2Poly:838`): the `Iff.rfl` bridge `bandFM_STEMn2Poly` (`Step2Gen:527`) at `(seqP, STFlow, bandFM∘STflowE, lemT∘z, sz.seqHflow n (t n) ω, zt (STflowE z n) (t n))` and the band-facts lemma `emn2Poly_bandFacts` (A: `h.1`; R: `seqHflow_isHermitian`, `etaT_pos`, `etaT_eq_zt_im`, `rfl`; S: `⟨sz.lam n, rfl⟩`; same proofs as `EMn2Poly:842-906`).

**T5′ `stEMn2ExpJgL_of`** (`EMn2Exp2`): `∀ d, 3 ≤ d → ∀ law Flow mk T0 Hf ζf`, `emn2ExpFacts → emn2ExpHK →` the chain of `Step2Gen:483` up to `∀ D>0`, then `∀ J : ℕ → sz.SeqΩ → ℝ, (∀ n ω, 0 ≤ J n ω) → PrecL (law sz) (U:=Unit) (n,ω ↦ STJhatg (mk sz z) n D (ℓ n) (t n) ω) ≺ (n,ω ↦ J n ω) →` `PrecL (law sz) ‖STEEg …‖ ≺ η⁻¹ (Bctl^{1/2} + (J n ω)³) (STprof sz n (t n) D (ℓ n) a₁ a₂)²`. It contains the paper form `(eq:MG_conclusion3_BA)` (`7_8:1999`: deterministic `J ≥ W^{-d}`, `Ĵ ≺ J`): `J ≥ W^{-d}` is not used, only `J ≥ 0`, and `J` may depend on `ω` (paper-delta candidate `T2404a`).
**T2 `stEMn2ExpgL_of`** (`EMn2Exp2`): `3 ≤ d → … → STEMn2ExpgL d law Flow mk T0` = T5′ at `J = STJhatg` (`≥ 0`: `sup'` of nonnegative quotients; `Ĵ ≺ Ĵ`: `StochDomAt.refl`, `Defs/StochDomAt:400`). Corollary `stEMn2Exp_holds d hd` (`EMn2Exp2:1090`): bridge `bandFM_STEMn2Exp` (`Step2Gen:530`) + `emn2Exp_bandFacts` + `emn2Exp2_bandHK`, the band proof of (HK) (`emn2Exp2_norm_STKloop` + `emn2Exp_kellStar_far` at `D+d`, `δ=1`, as `EMn2Exp2:939`). The consumers (`OptL2a/b`, `EtermsMid`, `MainIndHolds`, `MainIndOut`) see only `stEMn2Poly_holds`, `stEMn2Exp_holds`: unchanged.
**Intermediates** `emn2Exp_nearg`, `emn2Exp_far12g` (`EMn2Exp1`; conclusions in `emn2ExpS1/S2 (Hf …) …`, the matrix-level `S̃` of `EMn2Exp1:392-408`), `emn2Exp_far3g` (`EMn2Exp2`, with (HK) and `J`), `emn2Exp_of_far3g` (`EMn2Exp1`): the proofs of `emn2Exp_near :1206`, `emn2Exp_far12 :1465`, `emn2Exp_far3 :884`, `emn2Exp_of_far3 :1715` with the carrier reading of (iii). The four old names are listed in `T2404-check.lean` but have **no consumer outside the three files** (grep): if the dispatcher declares them frozen they stay as corollaries (`emn2ExpS1M` unfolds by `rfl` to `emn2ExpS1 (sz.seqHflow …) (zt …)`), cost in (iv).
Item 8 examples: at `baFMz sz0 zSeq`, `seqP (sz0.withLam 0)`, `BAFlow`, `BAflowT0`, `Hf = seqHflowBA (BAflowLam0 sz z) n (t n) ω`, `ζf = ztOf (BAmF …) (BAflowEs sz z n) (t n)`, with `emn2PolyFacts`, `emn2ExpFacts`, `emn2ExpHK` as hypotheses (statement level). **They need `import RBM3D.BA.FlowPins` (where `baFMz` lives, `FlowPins:393`) in `EMn2Exp2` only** (leaf: reverse cone 7 modules; the closure of `BA.FlowPins` has 66 modules, none `EMn2*`: no cycle): decision for the dispatcher (design L1: `FlowPins` then sits upstream of `DuhamelI/II`, `EtermsMid`, `MainIndHolds/Out`, `Main/BandTerminal`).

### (a′-iii) Band objects read, and the `rfl` question
```
$ cd scratchpad/T2404 && python3 kinds.py     # token occurrences outside the instance sections (docstring words included); the design count is 11 kinds / 230 mentions
Lloop (the loop 𝓛)                                                4  (EMn2Poly 1, EMn2Exp1 2, EMn2Exp2 1)
STEEk / STEEkM (the loop 𝓔⊗𝓔)                                    23  (EMn2Poly 10, EMn2Exp1 13, EMn2Exp2 0)
STflowE / lemT (energy, end of flow)                            101  (EMn2Poly 20, EMn2Exp1 61, EMn2Exp2 20)
etaT / zt / mE / mSigma (η, z_t, m)                              85  (EMn2Poly 17, EMn2Exp1 44, EMn2Exp2 24)
seqHflow (the matrix H_t)                                        23  (EMn2Poly 7, EMn2Exp1 9, EMn2Exp2 7)
STJhat / STJhatM (Ĵ)                                             18  (EMn2Poly 0, EMn2Exp1 6, EMn2Exp2 12)
STKloop / KLK / Theta (𝒦, Θ)                                     25  (EMn2Poly 0, EMn2Exp1 6, EMn2Exp2 19)
STFlow / v3_premises / ST_flow_im_pos (the flow predicate)       45  (EMn2Poly 4, EMn2Exp1 28, EMn2Exp2 13)
STInitialGT2 / STGM / STmaxLoop2 (G_t - M)                       17  (EMn2Poly 2, EMn2Exp1 13, EMn2Exp2 2)
Prec / STLWassm / STLWassmExp / ST_prec_* (law seqP)             31  (EMn2Poly 2, EMn2Exp1 27, EMn2Exp2 2)
SB (the kernel S)                                                21  (EMn2Poly 10, EMn2Exp1 11, EMn2Exp2 0)
ST_Bdata_holds / STBdata                                          3  (EMn2Poly 0, EMn2Exp1 2, EMn2Exp2 1)
TOTAL mentions (incl. docstring words) = 396
$ cd RBM3D/Induction && grep -c "pathH\|Hpath\|Classical.choose\|\.choose" EMn2Poly.lean EMn2Exp1.lean EMn2Exp2.lean
EMn2Poly.lean:0
EMn2Exp2.lean:0
EMn2Exp1.lean:0
```
Carrier reading of each kind: `Lloop`, `STEEk` become `C.L`, `STEEg C` (`Carrier:192`); `STflowE`, `lemT`, `STFlow` are not read (`T0`, `Flow`, facts H4, H5); `etaT`, `zt`, `mE`, `mSigma`, `seqHflow` appear only through `C.eta`, `ζf`, `Hf` (H1, H2; `mSigma`/`mE` also in the band proof of (HK)); `STJhat` becomes `STJhatg` (`Step2Gen:56`); `STKloop`, `KLK`, `Theta`, `kellStar` become (HK) (H7); `STInitialGT2`, `STGM`, `STmaxLoop2` become `STInitialGT2gL`, `C.GM`, `STmaxLoop2g` (`Carrier:76,135,140`); `Prec`, `STLWassm(Exp)`, `ST_prec_*` become `PrecL (law sz)`, `STLWassm(Exp)gL`, private `PrecL` copies (H13); `SB` becomes `C.S` plus (S) (H3); `ST_Bdata_holds` becomes (B) (H6).
`Iff.rfl`/`rfl` failures: **none predicted in the statements**. The four bridging identities are already compiled `Iff.rfl`/`rfl`: `STEEk ≡ STEEg (bandFM)`, `Prec sz ≡ PrecL (seqP sz)`, `STLWassm(Exp) ≡ …gL` (`bandFM_STEMn2Poly/Exp`, `Step2Gen:527,530`), `STJhat ≡ STJhatg` (`bandFM_STJhat`, `:276`); `emn2ExpS1M ≡ emn2ExpS1 (seqHflow)(zt)` is delta. What would fail is avoided by design: (1) an unfolding through `seqHflow`/`Lloop`/`zt`: `Hf, ζf` are passed, the proofs read `H` only through (R); the band instance is `rfl`, the BA instance `seqHflowBA`, `ztOf` (`BALloop = loopFine …` is `rfl`); (2) `Classical.choose`: absent from the files; it is the shape of `BAKloop = BAKsol` (`FlowPins:283`, `if h : ∃ … then h.choose`), which is never unfolded because `K` is read only through (HK) and the identification is `baK_unique` (`KSolve:568`) + `BAKsolve`, owed by the BA row; (3) `pathH`/`Hpath`: 0 occurrences; (4) band `if`: `STEEkM` and `STEEg` have the same `if k = 0`; `emn2ExpSw k` is carrier-free.

### (a′-iv) Predicted lines against the stop line 1,000, and I1
Components from the measured statement and proof sizes (`stmt.py`: lines of statement/proof and band-mention lines of `emn2Exp_near` 18/138 (7/33), `emn2Exp_far12` 19/133 (8/24), `emn2Exp_of_far3` 37/50 (16/22), `emn2Exp_far3` 20/174 (8/32), `stEMn2Poly_holds` 1/104 (0/29)): the generic theorem sits in the place of the old one (each band-mention line is one deletion plus one insertion), the old name is added after it as a corollary. A = inserted, R = deleted lines (the component values in `lines.py` are my estimates from these sizes):
```
$ cd scratchpad/T2404 && python3 lines.py
EMn2Poly  A= 117 R=  40 A+R= 157 A-R=  77
EMn2Exp1  A= 315 R= 110 A+R= 425 A-R= 205
EMn2Exp2  A= 331 R=  49 A+R= 380 A-R= 282
TOTAL     A= 763 R= 199 A+R= 962 A-R= 564   (+-25%: A+R in [721,1202])
if the four intermediates are not frozen (no old-name corollaries): A=645 A+R=844
5-prime extra lines (J-form vs target 2 direct): 40 central (hJ stmt 5, union event 14, monotone hS 6, exponent edits 8+8, rpow 4 ~ 35-60) vs I1 bound 80
```
Reading: `git diff --numstat` insertions `A ≈ 763`; deletions `R ≈ 199`; net growth `A-R ≈ 564`; `A+R ≈ 962` (range 721-1,202, ±25%). The ticket's estimate 500/650/900 comes from the design model (`T2379-design.md:145`, ST central 572); the design does not define which diff measure "net diff lines" is, so all readings are given. **No binding stop line is predicted to be hit on the central estimate under any of the three readings; the upper end of `A+R` (±25%) exceeds 1,000, so the 1b must report `git diff --numstat` after `EMn2Poly` and after `EMn2Exp1`, and split as T2a = `EMn2Poly` (target 1), T2b = `EMn2Exp1`+`EMn2Exp2` if the running `A+R` projects above 1,000.** Largest cut available: dropping the four old-name corollaries (`A+R ≈ 844`, if the dispatcher says they are not frozen). Per file `A+R`: `EMn2Poly` 157, `EMn2Exp1` 425, `EMn2Exp2` 380.
**I1: yes.** The `J` form costs about 40 extra lines (35-60): `J` hypothesis in the statement 5, second failure event by `StochDomAt.of_subset_union` (`Defs/StochDomAt:355`) 14, monotone replacement `Ĵ ≤ N^{τ/10} J` in the `(Ĵ+w)³` term 6, exponent edits (`τ_a = 10τ/13` so that `Y²N^{3τ_b} = N^τ`, or `A2 → A2 N^{3τ/10}` with `a = τ/5` in `ST_size_pow_big`) 8+8, `rpow` bookkeeping 4: below the bound 80. Target 5′ is adopted, with `STEMn2ExpgL` as its corollary. Exponent and instance check of the `J` form (`J = (W^{-d}B_{t,0})^{1/50}` is the paper's choice, `7_8:2010`; `cB = (𝔡⁻²+1)⁻¹`, `𝔡 = 1/10`, `t = 1/16`, sz0):
```
$ cd scratchpad/T2404 && python3 j.py
n=1e+06: log10 w=-94.5  log10 J=-1.89  J>=w: True  Bctl>=cB*w: True
n=1e+30: log10 w=-454.5  log10 J=-9.09  J>=w: True  Bctl>=cB*w: True
n=1e+60: log10 w=-904.5  log10 J=-18.09  J>=w: True  Bctl>=cB*w: True
tau 1/100 3*tau/10 = 3/1000 < tau/2 = 1/200 : True  slack exponent 1/500
tau 1/20 3*tau/10 = 3/200 < tau/2 = 1/40 : True  slack exponent 1/100
tau 1 3*tau/10 = 3/10 < tau/2 = 1/2 : True  slack exponent 1/5
```

### (a′-v) Verdicts (replace the “Verdicts” of (a) for the targets they name)
- **Target 1** (`stEMn2PolygL_of`): PASS. Hypotheses H1, H3, H4 only; all C1-clean; BA owes the public Hermitian lemma (row 15) and `SB d L 0 = 1`.
- **Target 2** (`stEMn2ExpgL_of`, `3 ≤ d`): PASS, as the `J = Ĵ` corollary of T5′; extra hypotheses H1-H6 and (HK).
- **Target 5′** (`stEMn2ExpJgL_of`): PASS; I1 answered yes (about 40 lines).
- (HK) is the one external input; its BA source is the composition of row 11 (mixed Θ of `baProp5_holds`, `M^{(σσ')}` of G3b/KKernel, `baK_unique`), not yet merged; `‖m‖=1` is not used anywhere. The limit computation is the `hk2.py` output above.
- Decisions requested of the dispatcher (none blocks the 1b): (1) are `emn2Exp_near/far12/far3/of_far3` frozen (≈118 inserted lines); (2) the `BA.FlowPins` import in `EMn2Exp2` for the item 8 BA examples; (3) the stop line reading (`A+R` or net).

## (b) Script output — Sun Oct 11 03:50:12 UTC 2026

**Line count against the stop line (ticket: net diff lines of the three files, stop 1,000).**
```
$ date -u; git log --oneline -1; git status --short | wc -l
Sun Oct 11 03:49:54 UTC 2026
65cf42f T2404: module notes, trims
0
$ for f in EMn2Poly EMn2Exp1 EMn2Exp2: wc -l on main and on t/T2404
EMn2Poly main=1028 branch=1078
EMn2Exp1 main=2122 branch=2286
EMn2Exp2 main=1295 branch=1531
$ git diff --numstat main...t/T2404 | awk (added, deleted; A+R, A-R)
297	133	RBM3D/Induction/EMn2Exp1.lean
323	87	RBM3D/Induction/EMn2Exp2.lean
104	54	RBM3D/Induction/EMn2Poly.lean
A=724 R=274 A+R=998 A-R=450
$ for c in $(git log --reverse --format=%h main..t/T2404): git diff --numstat main...$c | awk   (total per commit)
dc31b51: A=116 R=48 A+R=164 A-R=68
ea2eede: A=424 R=181 A+R=605 A-R=243
f2d17f8: A=699 R=264 A+R=963 A-R=435
e97b2d2: A=724 R=272 A+R=996 A-R=452
65cf42f: A=724 R=274 A+R=998 A-R=450
$ git diff --name-only main...t/T2404 | tr newline space
RBM3D/Induction/EMn2Exp1.lean RBM3D/Induction/EMn2Exp2.lean RBM3D/Induction/EMn2Poly.lean 
```
**Hypothesis table as finally used** (`(a′-i)` rows H1-H14; `hF.1 = emn2PolyFacts`, `hF.2` = (T),(E),(B) of `emn2ExpFacts`).

| 1a row | Lean hypothesis (declared) | read in | BA source / owner (C1 mark from `(a′-i)`) |
|---|---|---|---|
| H1 (R) | Hf Hermitian, `Im ζf = eta > 0`, `C.L = loopFine Hf ζf` (`emn2PolyFacts`, Poly:835) | T1, nearg, far12g, far3g, T5′ split | clean; `BALloop` is `loopFine seqHflowBA ztOf`; public Hermitian lemma owed (private at `FlowPins:925`) |
| H3 (S) | `∃ g, C.S n = SB d L g` (Poly:835) | T1 (`emn2Poly_EEg_zero_eq`), T5′ split | clean; BA `S = 1`: `SB d L 0 = 1` owed |
| H4 (A) | `Admissible` (Poly:835) | all | clean (`BAFlow.1`) |
| H5 (T), H2 (E) | `T0 < 1`; `eta n u ≤ 1 - u` (`emn2ExpFacts`, Exp1:811) | far3g (`ht1`, `hηv`), T5′ (`STBctl_pos`) | clean (`BAt0_lt_one`; `Im m ≤ ‖m‖ ≤ 1`) |
| H6 (B) | `∃ cB c, ∀ᶠ n, ∀ u ≤ T0, cB W^{-d} ≤ Bctl ≤ N^{-c}` (Exp1:811) | nearg, far12g, far3g | clean; owed by the BA twin from `WO`, `Bandwidth`, `BAdom` |
| H7 (HK) | `emn2ExpHK` (Exp2:934) | far3g (`hK`), T5′, T2 | owed: `(Kn2sol)` + `BAProp5` composition, not merged |
| H8, H9 | `ekPropTInf_holds`, `emn2Exp2_exists_CR`: reused unchanged | far3g (`hTTT`, `hrad`) | model-free |
| H10 | `emn2Exp_kellStar_far` | band `emn2Exp2_bandHK` only | n/a |
| H11 | `STInitialGT2gL`, `STLWassmgL`, `STLWassmExpgL` | premises of the pins; hypotheses of the examples | other gates' pins |
| H12-H14 | model-free lemmas reused; private copies `emn2Exp_precL_mono/_sup` (Exp1:859, :866), `emn2Exp2_Jhatg_nonneg` (Exp2:798) | nearg, far3g | clean |

**Build, check file, axioms.**
```
$ TZ=UTC git log -1 --format="commit %h at %cd" --date=format-local:%H:%M:%S; TZ=UTC stat -f "%N %Sm" -t %H:%M:%S build logs
commit 65cf42f at 03:40:01
build_three.log 03:42:13
build_full.log 03:43:30
$ lake build RBM3D.Induction.EMn2Exp2 RBM3D.Induction.OptL2b RBM3D.Induction.DuhamelII | tail -2
✔ [3912/3912] Built RBM3D.Induction.DuhamelII (35s)
Build completed successfully (3912 jobs).
$ lake build   (the full library, with #assert_rbm_axioms): errors, sorry, last line
errors=0 sorry=0
Build completed successfully (4212 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" the three files | wc -l
0
$ lake env lean docs/tickets/checks/T2404-check.lean >/dev/null; echo exit $?
exit 0
$ lake env lean ax_all.lean  (20 #print axioms + G1: example (d) : STEMn2Poly d := stEMn2Poly_holds d; example (d) (hd : 3 ≤ d) : STEMn2Exp d := stEMn2Exp_holds d hd)
exit 0
20 declarations, axioms [propext, Classical.choice, Quot.sound]: stEMn2PolygL_of, emn2Poly_bandFacts, stEMn2Poly_holds, emn2Poly_EEg_zero_eq, emn2Poly_EEg_one_eq, emn2Exp_bandFacts, emn2Exp_nearg, emn2Exp_near, emn2Exp_far12g, emn2Exp_far12, emn2Exp_EEg_split, emn2Exp_assemble, emn2Exp_of_far3, emn2Exp2_loop2_far_leg, emn2Exp2_bandHK, emn2Exp_far3g, emn2Exp_far3, stEMn2ExpJgL_of, stEMn2ExpgL_of, stEMn2Exp_holds
output lines that are not #print axioms lines: 0
$ lake env lean check_prem.lean  (STEMn2ExpgL d law Flow mk T0 ↔ emn2ExpPrem d law Flow mk T0 (J = Ĵ conclusion) := Iff.rfl)
exit 0
```
**Targets and facts-definitions (extracted by script), compiled instances, name clashes, ports.**
```
$ python3 extract2.py   (declaration text from the files, whitespace collapsed; defs to the blank line)
EMn2Poly:859 theorem stEMn2PolygL_of {d : ℕ} (law : ∀ sz : Sizes d, Measure sz.SeqΩ) {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} {Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {ζf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), ℂ} (hF : emn2PolyFacts d Flow mk T0 Hf ζf) : STEMn2PolygL d law Flow mk T0 := by
EMn2Poly:835 def emn2PolyFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ζf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), ℂ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → sz.Admissible 𝔠 𝔡 ∧ (∀ (n : ℕ) (u : ℝ), 0 ≤ u → u ≤ T0 sz z n → (∀ ω, (Hf sz z n u ω).IsHermitian) ∧ 0 < (ζf sz z n u).im ∧ (ζf sz z n u).im = (mk sz z).eta n u ∧ ∀ (ω : sz.SeqΩ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), (mk sz z).L n u σ a ω = loopFine d (sz.L n) (sz.W n) (Hf sz z n u ω) (ζf sz z n u) σ a) ∧ (∀ n : ℕ, ∃ g : ℝ, (mk sz z).S n = SB d (sz.L n) g)
EMn2Exp1:811 def emn2ExpFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ζf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), ℂ) : Prop := emn2PolyFacts d Flow mk T0 Hf ζf ∧ ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → (∀ n, T0 sz z n < 1) ∧ (∀ (n : ℕ) (u : ℝ), 0 ≤ u → u ≤ T0 sz z n → (mk sz z).eta n u ≤ 1 - u) ∧ ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T0 sz z n → cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)
EMn2Exp1:826 def emn2ExpPrem (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Q : ∀ (sz : Sizes d) (z : ℕ → ℂ) (t ℓ : ℕ → ℝ) (D : ℝ), Prop) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧ Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) → STInitialGT2gL (mk sz z) (law sz) t ε₀ Ψ → ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) (t n)) → (∀ D : ℝ, 0 < D → STLWassmExpgL (mk sz z) (law sz) t D ℓ) → ∀ D : ℝ, 0 < D → Q sz z t ℓ D
EMn2Exp2:934 def emn2ExpHK (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop, ∀ (x x' : Zd d (sz.L n)) (s : Bool), emn2ExpEllStar sz n (t n) ≤ (zdistInf d (sz.L n) (x - x') : ℝ) → ‖(mk sz z).K n (t n) ![s, !s] ![x, x']‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-(D + (d : ℝ)))
EMn2Exp2:1226 theorem stEMn2ExpJgL_of (hd : 3 ≤ d) (hF : emn2ExpFacts d Flow mk T0 Hf ζf) (hHK : emn2ExpHK d Flow mk T0) : emn2ExpPrem d law Flow mk T0 (fun sz z t ℓ D => ∀ J : ℕ → sz.SeqΩ → ℝ, (∀ n ω, 0 ≤ J n ω) → PrecL sz (law sz) (U := fun _ => Unit) (fun n _ ω => STJhatg (mk sz z) n D (ℓ n) (t n) ω) (fun n _ ω => J n ω) → PrecL sz (law sz) (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖STEEg (mk sz z) n (t n) p.1 p.2.1 p.2.2 ω‖) (fun n p ω => ((mk sz z).eta n (t n))⁻¹ * ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) + (J n ω) ^ 3) * (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2)) := by
EMn2Exp2:1260 theorem stEMn2ExpgL_of (hd : 3 ≤ d) (hF : emn2ExpFacts d Flow mk T0 Hf ζf) (hHK : emn2ExpHK d Flow mk T0) : STEMn2ExpgL d law Flow mk T0 := by
EMn2Exp2:1274 theorem stEMn2Exp_holds (d : ℕ) (hd : 3 ≤ d) : STEMn2Exp d :=
EMn2Poly:989 theorem stEMn2Poly_holds (d : ℕ) : STEMn2Poly d :=
$ python3 inst.py   (instances: file:line, application term after the example statement)
EMn2Poly:1018 stEMn2PolygL_of (fun sz => Sizes.seqP sz) (emn2Poly_bandFacts 3) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20) (by norm_num) Ψ0 Ψ0_class hI
EMn2Exp2:1458 stEMn2ExpgL_of (fun sz => Sizes.seqP sz) (by norm_num) (emn2Exp_bandFacts 3) (emn2Exp2_bandHK 3 (by norm_num)) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth
EMn2Exp2:1476 stEMn2ExpJgL_of (fun sz => Sizes.seqP sz) (by norm_num) (emn2Exp_bandFacts 3) (emn2Exp2_bandHK 3 (by norm_num)) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteent
EMn2Exp2:1522 stEMn2PolygL_of (fun sz => Sizes.seqP (sz.withLam 0)) hF.1 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 have _ := stEMn2ExpgL_of (fun sz => Sizes.seqP (sz.withLam 0)) (by norm_num) hF hHK (1 / 2) (1 / 10) (1 / 1
$ git grep -n -w <the 21 new public names> main -- RBM3D docs/tickets/checks | wc -l ; the same by grep -rn on t/T2404 outside the three files
main: 0  branch outside the three files: 0
$ git diff main...t/T2404 | grep "^+" | grep -c "RBM1D\|RBM2D"   (ports: none)
0
```

**Narrative.**
- T1 `stEMn2PolygL_of` (EMn2Poly:859) is the band proof of `stEMn2Poly_holds` with `Lloop`, `etaT`, `seqHflow`, `SB … (sz.lam n)` read through `emn2PolyFacts`; `stEMn2Poly_holds` (:989) is `bandFM_STEMn2Poly` applied to it and `emn2Poly_bandFacts` (:971). The matrix-level lemmas are unchanged.
- T5′ `stEMn2ExpJgL_of` (EMn2Exp2:1226) assembles `emn2Exp_nearg` (Exp1:1287), `emn2Exp_far12g` (:1580) and `emn2Exp_far3g` (Exp2:977) with `emn2Exp_EEg_split` (Exp1:1831) and `emn2Exp_assemble` (:1872). T2 `stEMn2ExpgL_of` (:1260) is T5′ at `J = Ĵ`; `stEMn2Exp_holds` (:1274) is `bandFM_STEMn2Exp` applied to it, `emn2Exp_bandFacts` (Exp1:843) and `emn2Exp2_bandHK` (Exp2:945).
- I1: yes. The `J` form needs in `emn2Exp_far3g`: the failure event as a union (`StochDomAt.of_subset_union`) at level `τ/10`; the 2-loop bound at `τ/5` by monotonicity (`N ≥ 1`); `Ĵ ≤ N^{τ/10} J`; the loss `y³` absorbed in `A₂' = y³ A₂`; `2(A₁+A₂'+1) ≤ y³ N^{τ/5} = y⁵`. `emn2Exp2_assemble` is unchanged.
- The four old names stay: `emn2Exp_near`, `emn2Exp_far12`, `emn2Exp_far3` are corollaries (`intro` then `exact` of the generic theorem at the band; a one-term proof of the whole statement hit the 200000 heartbeat limit in my first build). `emn2Exp_of_far3` keeps its band statement and now calls `emn2Exp_assemble`. No `maxHeartbeats` option was added; one `set_option linter.unusedVariables false` is in EMn2Poly.
- Decisions of `(a′-v)`: (1) the four names kept; (2) `import RBM3D.BA.FlowPins` is in `EMn2Exp2` only (item 8); the full `lake build` passes; (3) the stop line is not hit under any of the three readings (A=724, net 450, A+R=998).
- Differences from the text of `(a′-ii)`: `Hf`, `ζf` take the time `u : ℝ` (`Hf sz z n u ω`), the facts read `0 ≤ u ≤ T0 sz z n`, and (B) is stated up to `T0`; `emn2ExpPrem` is the premise block of the pin (`check_prem`: `Iff.rfl` with `STEMn2ExpgL`); (HK) is as in `(a′-ii)`. The BA-carrier examples are at `sz0`, `zSeq`, `flow_sz0` with the facts and (HK) as hypotheses (no BA proof is owed here).
- The band lemmas `emn2Exp2_loop2_far_le`, `emn2Exp2_STLKM_le` are no longer read by any theorem (the band example at EMn2Exp2:1408 uses the first); `emn2Exp_EEk_cover/_split` are still read by `emn2Exp_of_far3`.

## (c) Verified Mathlib and project names (all `#check`ed in the scratch file `chk_names.lean`)
`Finset.lt_sup'_iff`, `Finset.univ_nonempty`; `inv_nonneg`, `le_add_of_nonneg_right`; `sub_add_cancel`, `sub_nonneg`; `Real.one_le_rpow`, `pow_le_pow_left₀`; `one_le_pow₀`, `mul_le_of_le_one_right`; `Real.rpow_le_rpow_of_exponent_le`; tactic `linear_combination` on a `≤` goal; project: `StochDomAt.of_subset`, `StochDomAt.of_subset_union` (`Defs/StochDomAt:325,355`).
Verified absent on `main`: a `PrecL` form of `ST_prec_mono_eventually` / `ST_prec_sup` (`git grep` finds only the `Prec sz` forms, `Step2Events:49,76`); a carrier form of `ST_JhatM_nonneg`.

## (d) Open issues and paper-delta candidates
- **T2404a** (paper-delta): `stEMn2ExpJgL_of` drops `J ≥ W^{-d}` of `(eq:MG_conclusion3_BA)` (`7_8:1999`) and allows `ω`-dependent `J` with `Ĵ ≺ J`; the BA pin REQ (C7) may use it.
- **T2404b**: the generic statements are conditional on `emn2PolyFacts`, `emn2ExpFacts`, `emn2ExpHK` (explicit hypotheses; the paper reads them as properties of the model). Owed by the BA twin of T2, none merged: public Hermitian lemma for `seqHflowBA`; `SB d L 0 = 1`; (B); the (HK) composition.
- The margin to the stop line is 2 (A+R=998): later edits of these three files must remove the dead band lemmas first.
- `emn2Exp_far3g` keeps the old docstring line that names `emn2Exp2_loop2_far_le` (the generic form is `emn2Exp2_loop2_far_leg`).
- T2405 (HK reuse): the name is `emn2ExpHK` (Exp2:934); `git log main..t/T2405` was empty when `(a′)` was written (not re-checked).
