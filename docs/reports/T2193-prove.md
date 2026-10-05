Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 15:19:27 UTC 2026

**Verdict: target 1 PASS; target 2 FAIL (the grid error needs a floor on the right side of `GijGEX`; the ticket's stop rule applies); target 3 BLOCKED on target 2 (`E2Hyp` conjunct (P-e7/8)). Stage 1b must not start; split S5-09a (DECISIONS §63).**

### (i) Exponent table
Notation: `N = (WL)^d`, `x_u = W^d(1-u)`, `P = L^dW^{6d}`, `Θ`-form constants as in `Path/LemDecCalE.lean:44-110`.

| # | constant | value | constraint | slack / source |
|---|---|---|---|---|
| 0a | `τ'` | `min(τ/10, 1/D)` | `N^{τ'} ≤ W^{1/2}` (M3) and `9τ' < τ` (loss row 5) | `P² ≤ W^D`, `N = W^dL^d ≤ P` (`W ≥ 1`) give `N ≤ W^{D/2}`, `N^{τ'} ≤ W^{Dτ'/2} ≤ W^{1/2}`. Slack in `9τ'`: `τ/10`. |
| 0b | `J` | `N^{τ'}·Jst n u D` | `1 ≤ J ≤ W` (`E2Hyp` conjunct 15, `LemDecCalE.lean:84`) | `Jst ≥ 1` gives `J ≥ 1`; `Jst ≤ W^{1/2}` (target 1) and 0a give `J ≤ W^{1/2}W^{1/2}`. **Row 0 verdict: PASS.** |
| 1 | `Λ` | `32·N^{τ'}` | `≥ √2 N^{τ'/2}` (e6), `N^{τ'}` (e7/8), `2N^{τ'}` (e9), `4,8,32 N^{τ'}` (3-,4-,6-loop) | Constants `2^{k-1}` from `Bctl ≤ 2x_u^{-1}`, i.e. `Bparam ≤ 2(1-u)⁻¹` (`kellStar_bparam_le`, `Path/KellStar.lean:68`, private: restate). Tight at `k = 6`. |
| 2 | `K₀` | `1` | `‖𝒦^{(2)}_{(+,-),(a,b)}‖ ≤ K₀ x_u⁻¹` | `𝒦 = W^{-d}Θ_u(a,b)` (`lemDecCalE_STKloop_two`, `LemDecCalE.lean:1275`, `|m|=1`) and `sum_norm_Theta_row_le` (`Propagator/Props4.lean:210`) give `≤ (1-u)⁻¹W^{-d}`. Exact. |
| 3 | `c` of `AsGMcPT` | `𝔡` (ticket expected `𝔡/2`; both close) | `√2 N^{τ/2}W^{-𝔡} ≤ N^τ W^{-c}` | `STWB ≤ 2x_u⁻¹ ≤ 2(lam²W^d)⁻¹ ≤ 2W^{-2𝔡}` (`lam_sq_mul_pow_ge`, `Defs/Sizes.lean:193`); needs `N^{τ/2} ≥ √2`, eventually. |
| 4 | Kell range | `δ = 1/8`, `D` as in the pin, `Λ_K = 𝔡⁻¹`, `τ_K = ε/2` | `kellStarEv` hypotheses (`Path/KellStar.lean:52`) | `SizeTendsto`, `Bandwidth 𝔠` from `Admissible`; `lam ≤ 𝔡⁻¹` from `WO` (`Defs/Sizes.lean:164`); `RangeCond (ε/2) t` from `v3_premises_of_stFlow` (`Green/Pins.lean:1049`). The range `δ(log W)^{3/2}ellT` is the same expression in `kellStarEv` and `E2Hyp`, so no `ellT = 1` is needed (it holds anyway: `lam² ≤ 1-u` gives `lam/√(1-u) ≤ 1`, `ellT = min(max(·,1),L) = 1`). |
| 5 | loss | `lossE2dif·N^{3τ'}`, `lossE2wG·N^{3τ'/2}`, `lossE2·N^{2τ'}` | `≤ N^τ` eventually | `Λ⁶J³ = 32⁶N^{9τ'}Jst³`, `Λ⁶J^{3/2}` gives `N^{7.5τ'}`, `Λ⁶J²` gives `N^{8τ'}`. Rest: `10¹²(1600d⁴)^dK₀²·(1+log(L^dW^{2d}))⁴(1+log W)³e^{8(log W)^{3/4}}·729^d(1+log P)^{2d}`; `log P ≤ 6 log N`, `log W ≤ log N`: `N^{o(1)}` (`tendsto_size`). Slack `N^{τ-9τ'} ≥ N^{τ/10}`. |
| 6 | floor | `(L^dW^{6d})² ≤ W^D` | `L^dW^{2d} ≤ W^D` (`E2Hyp`), and the floors of `E2HypDif`/`E2HypWG` | `L^dW^{2d} ≤ P ≤ P²` (`P ≥ 1`); the floor of `E2HypDif`/`E2HypWG` is the pin's floor verbatim. At `sz0`, `D = 42`: `P² = L⁶W³⁶ ≤ W⁴²` iff `L ≤ W` (`sz0_L_le_W`, `Defs/Sizes.lean:272`). |
| 7 | event count | 7 events (ticket says 6) | `7N^{-D₁-1} ≤ N^{-D₁}` eventually | `hLK`, `STLocalEntryU`, target 2, `STAvgU`, `STLmaxU` at `k = 3, 4, 6`. Correction to the ticket text only. |

### Conjunct → source table (`E2Hyp` 20 conjuncts, then the `E2HypDif`/`E2HypWG` extras), at `M = seqHflow n u ω`, on `Ω_n`
| conjunct | source | status |
|---|---|---|
| `3 ≤ d`; `|E|<2`; `0 ≤ u<1` | hyp; `v3_premises_of_stFlow` (`|E| < 2-κ/2`); `s ≥ 0`; `st5_t_lt_one` (`Step5Kit.lean:192`) | ok |
| `0<lam`; `lam² ≤ 1-u`; `1 ≤ lam²W^d`; `4 ≤ log W` | `st5_eventually_A_ge_one` (`Step5Kit.lean:200`, WO); `STReg5III` with `u ≤ t`; `lam_sq_mul_pow_ge`; `W ≥ N^𝔠 → ∞` (`Bandwidth`, `SizeTendsto`) | ok (eventually) |
| `1 ≤ Λ`, `1 ≤ K₀`, floor | rows 1, 2, 6 | ok |
| Hermitian | `seqHflow_isHermitian` | ok |
| (P-e6) | `STLocalEntryU` + `STWB ≤ 2x_u⁻¹`, `x_u ≥ 1` so `x_u^{-1/2} ≤ x_u^{-1/4}` | ok, `Λ ≥ √2N^{τ'/2}` |
| **(P-e7/8)** `p ≠ q` | target 2 (`GijGEXPTSwap` uniform in `u`, `gexRHS` of `E2Hyp` at `[q],[p]`) | **missing: row (3) below** |
| (P-e9) both `σ` | `STAvgU` (`σ : Fin 1 → Bool`, both signs) | ok, constant 2 |
| `1 ≤ J ≤ W`; `‖STLKM‖ ≤ J·T_{u,D}` | rows 0a, 0b; `hLK` at `τ'` and `STLM_seqHflow` | ok |
| `𝒦` bound; (`Kell*`) | row 2; `‖𝒦‖ = W^{-d}‖Θ_u‖ ≤ ‖Θ_u‖ ≤ W^{-D}` from `kellStarEv` (`s = 0`), bridge via `lemDecCalE_STKloop_two` and `m·m̄ = 1` | ok (bridge re-verified here) |
| `E2HypDif`: `|𝓛^{(4)}| ≤ Λx^{-3}`, `|𝓛^{(6)}| ≤ Λx^{-5}`; `E2HypWG`: `|𝓛^{(3)}| ≤ Λx^{-2}` | `STLmaxU` at `k = 4, 6, 3` with `Bctl^{k-1} ≤ (2x_u⁻¹)^{k-1}` | ok, `Λ = 32N^{τ'}` |

### Row (3), M2: the net lift of target 2 does not close without a floor
Route (i)-(ii) is sound: `gbEXPV3` at `(sz, κ/2, 𝔠, 𝔡, ε/2)`, premises from `v3_premises_of_stFlow`, `gijGEXPTSwap_giiGEXPT_of_V3` (`Green/Pins.lean:310`) needs `AsGMcPT sz E s t 𝔡` (row 3), giving `GijGEXPTSwap` per time (no indicator).
Net lift. Per entry: `x(u) := |G_{pq}(u)|²`, `ρ(u) := gexRHS(u)`. `H_u = √u X` (`seqHflow`, `Gauss/FineModel.lean:227`). The copied helpers give, with `Q ≥ (η_t)⁻¹` and `Xb ≥ ‖X‖`: `|G_{xy}(u)-G_{xy}(u')| ≤ Q²(Xb+1)√|u-u'| =: η_G` (`nl2_entry_diff`, `Path/NetLift2.lean:289`) and, for the 2-loop (`card Vtx = N`), `|𝓛(u)-𝓛(u')| ≤ N·2·Q²·(Q²(Xb+1)√|u-u'|)` (`nl2_loop_sub`, `:136`). A grid of polynomial size (`exists_netPt_close`, `Gauss/Domination.lean:166`; `stochDomAt_of_perTimeDomAt`) makes `η_G ≤ N^{-A'}` for any fixed `A'` once `Q`, `Xb` are powers of `N` (the bound on `‖X‖` is not checked here).
Absorption attempt, grid point `u_k`, `ρ = gexRHS`: `x(u) ≤ 2x(u_k)+2η_G² ≤ 2N^τρ(u_k)+2η_G²`. With `Eblk = W^{-d}·1_block` (`Loop/GLoop.lean:55`), `loopPM(a,b) = W^{-2d}Σ_{x∈[b],y∈[a]}|G_{xy}|²` (a sum of `W^{2d}` squares of entries), so the entrywise inequality `|g'|² ≤ 2|g|²+2η_G²` gives `ρ(u_k) ≤ 2ρ(u) + 2·9^d η_G²` (the `W^{-d}1(|a-b|≤1)` term does not depend on `u`). Hence
`x(u) ≤ 4N^τ ρ(u) + C_d N^τ η_G²`, with an **additive** `N^τ η_G²`.
To drop it one needs `ρ(u) ≳ η_G² = N^{-2A'}` at the bad `u`. The only lower bounds on `ρ` in the files are `ρ(u) ≥ loopPM([q],[p]) ≥ W^{-2d}x(u)` (loses `W^{2d} ≫ N^τ`) and `ρ ≥ W^{-d}` for `|a-b| ≤ 1`. For `|a-b| > 1` the right side is a sum of `|loops|` with no lower bound: by (`Kell*`) `𝒦 ≤ W^{-D}` for every `D` beyond `(log W)^{3/2}/8`, and `T_{u,D}` carries `e^{-√r}`. Making `η_G` smaller does not help: the error stays additive while `ρ(u)` is not bounded below. A multiplicative comparison would need the convolution structure `(G²)_{pq} = Σ_x G_{px}G_{xq}` (`∂_uG = αG + β(G²)`, `H_u = √u X`), i.e. a decay bootstrap, not a net.
Consequence: the uniform statement `LemDecCalEPrec_gijU_shape` (`ρ` exactly `gexRHS`) follows from the per-time one only up to `+ N^{-A}`, and `E2Hyp` conjunct (P-e7/8) has no such slot (`Path/LemDecCalE.lean:79-81`; `E2Hyp`, `E2HypDif`, `E2HypWG` may not be changed here). **Ticket stop rule: "if the lift needs a floor `W^{-D}` on the right side, stop and report".** Options for the dispatcher (not verified here): (a) S5-09a proves a primed `E2Hyp'` with `Λ ρ + W^{-D'}` in (P-e7/8) and re-derives the three `lemDecCalE_*` (`T_{u,D} ≥ W^{-D}` may absorb it; re-check each use of clause 4 in `LemDecCalE*.lean`); (b) a multiplicative lift by decay bootstrap.

### Row (6), consumer check (script output)
```
$ diff <(STLemDecCalEConcl body, Step5Pins.lean:161-186) <(STLemDecCalEConcl_new_pin body, checks/T2193-check.lean)
2c2,4
<     ∀ D : ℝ, 0 < D → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
---
>     (∀ n u D, Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) →
>     ∀ D : ℝ, 0 < D →
>       (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
$ grep -rn "STLemDecCalEConcl\|STLemDecCalE\b\|inst_lemDecCalE" RBM3D --include="*.lean"   (compile uses)
Step5Pins.lean:161 def; :191 STLemDecCalE := STIngR5 d STReg5III (fun sz E s t => STLemDecCalEConcl sz E s t); :594-595 inst_lemDecCalE
(others: Test/Axioms.lean:177 owed line; docstrings in LemDecCalE.lean:35,97, LemDecCalEdif.lean:78, LemDecCalEwG.lean:79, Step5Pins.lean:19)
```
Target 1 only weakens (two added premises, floor changed); `STLemDecCalE` and `inst_lemDecCalE` are generic in `Concl` and keep their text. Target 1 PASS. Downstream note for S5-10: use `D' = max(D, D₀)` (`T_{u,D}` decreases in `D`) and supply `Jst ≤ W^{1/2}` from the stopping time `J* < W^ε`, `ε < 1/2`.

### (ii) One concrete nondegenerate instance (target 1 and the deterministic hypotheses of target 3)
Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))⁵`, `lam = (2(n+1))⁻⁶`, `Defs/Sizes.lean:260`), `s = 0`, `t = 1/16`, `𝔡 = κ = ε = 1/10`, `D = 42`, `Jst ∈ {1, W^{1/2}}`, `τ ∈ {1/10, 1}`.
```
$ python3 <scratchpad>/T2193/inst.py     (exact Fraction arithmetic for the floor, N ≤ P, lam²W^d, M3)
n=1: L=8 W=1024 N=2^39.0 lam=2.441e-04 lam^2W^3=64.0 logW=6.93 floor ratio P^2/W^42=2.274e-13 N^(1/42)=1.903 sqrtW=32.0 dist-threshold (1/8)(logW)^1.5=2.281 (L=8)
   STWB bound 2/(W^d lam^2)=3.125e-02 <= 2W^(-2*0.1)=5.000e-01; ...
n=5: L=24 W=248832 N=2^67.5 lam=3.349e-07 lam^2W^3=1728.0 logW=12.42 floor ratio P^2/W^42=8.051e-25 N^(1/42)=3.048 sqrtW=498.8 dist-threshold (1/8)(logW)^1.5=5.474 (L=24)
   STWB bound 2/(W^d lam^2)=1.157e-03 <= 2W^(-2*0.1)=1.667e-01; ...
Lambda const needed: P-e6 sqrt2, P-e7/8 1, P-e9 2, 3-loop 4, 4-loop 8, 6-loop 32 -> C1=32: [4, 8, 32]
tau=1.0 lk: loss*N^(m tau')<=N^tau for all n >= 10^15
tau=1.0 wG: loss*N^(m tau')<=N^tau for all n >= 10^19.2
tau=1.0 dif: loss*N^(m tau')<=N^tau for all n >= 10^21
tau=0.1 lk: loss*N^(m tau')<=N^tau for all n >= 10^1.33e+07
tau=0.1 wG: loss*N^(m tau')<=N^tau for all n >= 10^5.47e+06
tau=0.1 dif: loss*N^(m tau')<=N^tau for all n >= 10^2.13e+08
```
The script asserts (all passed): floor `P² ≤ W⁴²`, `L^dW^{2d} ≤ P²`, `N ≤ P`, `lam² ≤ 1-1/16`, `lam²W^d ≥ 1`, `WO` (`W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`), `log W ≥ 4`, `N^{τ'} ≤ W^{1/2}`, `1 ≤ J ≤ W` for both `Jst`, `ellT = 1`. The index set `STIdx2` is nonempty (`[0,1/16] × {±}² × (Z_L³)²`); the (`Kell*`) range `(1/8)(log W)^{3/2}` is `2.28 < L = 8` at `n = 1` (not vacuous). The `∀ᶠ` floor holds at every `n` of `sz0` since `L ≤ W`; as `n → ∞`, `P²/W⁴² = (L/W)⁶ → 0`.
External-hypothesis limit check (the stochastic premises `hLK`, `STLocalEntryU`, `STAvgU`, `STLmaxU` stay hypotheses): the only limits used are `N → ∞`, `W → ∞`, `(log W)^{3/4} = o(log N)`; the thresholds above are the `≺`-absorption of the explicit loss in the conclusion (an "eventually" claim: `τ` is universally quantified), not a hypothesis of any target.

### Verdicts
- **Target 1 (pin change): PASS.**
- **Target 2 (`LemDecCalEPrec_gijU`): FAIL**: the net-lift absorption needs a floor on `gexRHS` (row 3); stop after 1a per the ticket.
- **Target 3 (`stLemDecCalE_holds`): BLOCKED** on target 2: `E2Hyp` conjunct (P-e7/8) has no source on `Ω_n`; every other conjunct is `ok` (table above), rows 0-2, 4-6 close.

## (a′) Preflight corrections — Mon Oct  5 19:07:39 UTC 2026

Stage 1b with `docs/tickets/T2193-amend-1.md`: re-check of (P), (N), (C) and the `J♯` bookkeeping against the compiled lemmas of `RBM3D/Induction/LemDecCalEPrec.lean` (prefix `lemDecCalEPrec_` written `·`) and the script `ap.py` (output in (b)). Superseded by Amend 1: (a) row (3) and the verdicts "target 2 FAIL / target 3 BLOCKED". Constants changed from (a): row 0a `τ′ = min(τ/24, 1/(2D))` (was `min(τ/10, 1/D)`), row 5 loss `≤ N^{τ/2}` with `Λ = 32 N^{τ′}` and no power of `J`. No line failed; no verdict of (a) changes.
| line | re-check | lemma | status |
|---|---|---|---|
| (P) events at fixed `(n,u)` | 7: hLK at `τ′` (`STLK2 ≤ N^{τ′} Jst T`), `STLocalEntryU`, `GijGEXPTSwap`, `STAvgU`, `STLmaxU` at `k = 3,4,6` | `·good`, `·prob` | ok |
| per-time union | `GijGEXPTSwap` (`gbEXPV3`, `AsGMcPT` at `c = 𝔡` from `STLocalEntryU`) over `#(Idx×Idx) = N²` pairs at `D₁+3`, the six `Prec` events at `D₁+1`: `≤ 7N^{-(D₁+1)} ≤ N^{-D₁}` for `N ≥ 7` | `·asGMcPT`, `·gij`, `·prob` | ok |
| loss, `J♯` kept in `ζ` | `lossE2 ≤ lossE2dif ≤ lossE2wG ≤ A_d N^{6τ′}(1+6 log N)^{7+2d} e^{8 (log N)^{3/4}} ≤ N^{τ/2}` for `6τ′ ≤ τ/4`, `A_d = 10¹²(1600d⁴)^d 32⁶ 1000^d`; `J` is not in the loss | `·loss_mono`, `·lossWG_le`, `·lossWG_eventually` | ok |
| `J♯` | `1 ≤ J♯` (`basic.1`); `J♯ ≤ N^{τ′} Jst` on `good` (`basic.3`, `X = N^{τ′}Jst ≥ 1`); `N^{τ′} ≤ W^{1/2}` from `N ≤ L^dW^{6d} ≤ (L^dW^{6d})² ≤ W^D`, `Dτ′ ≤ 1/2`; with `Jst ≤ W^{1/2}`: `J♯ ≤ W` | `·QW`, `·goodDet` | ok |
| `m_i`, `R₀ᵢ`, `Rᵢ` | `m = 2, 3/2, 3`; `R₀₁ = 0`; `R₀₂ = (1-u)⁻¹ 1(|a₁-a₂| ≤ (log W)^{3/2}) T`, `R₀₃` the same with `4(log W)^{3/2}` and `T²`; `R₁ = (1-u)⁻¹(W^d|1-u|)⁻¹T`, `R₂ = (1-u)⁻¹(W^d|1-u|)^{-1/2}T`, `R₃ = R₂` with `T²` | `·R1…R3`, `·Bounds` | ok |
| floors | `Rᵢ ≥ N^{-(1+2D)}` (`CR = 1+2D`), `R₀ᵢ ≥ 0` | `·floor`, `·R0_nonneg` | ok |
| relative continuity | `ρ⁴` for `R₁, R₂₀, R₂`, `ρ⁶` for `R₃₀, R₃` (`LemDecCalELip_relcont`); `ρ^k ≤ 1 + N^{2k}√|u-u′|` (`N ≥ 2`); `J♯`: `LemDecCalELip_Jsharp_rel`; `C = max(C_ξ, C_J, 2k)` | `·rel`, `·pow_rel`, `·lift` | ok |
| T2198 premises at `E = STflowE z` | `|E_n| ≤ 2 - κ/2` and `t_n < 1` (`v3_premises_of_stFlow`), `0 ≤ s_n` (hyp), `(1-t_n)⁻¹ ≤ N` eventually (`lam² ≤ 1-t`, `1 ≤ lam²W^d`, `W^d ≤ N`) | `·htN` | ok |
| (C) | `τ″ = τ/(m+1)`, `τ″(1+m) = τ`; on the event of hLK `J♯(u) ≤ N^{τ″}Jst(u)` for every `u` at once | `·combine` | ok |
| conjunct constants | `X = (W^d(1-u))⁻¹ ≤ 1`, `STWB, B_{u,0} ≤ 2X`: `‖G-m‖ ≤ √(2N^{τ′}X) ≤ 32N^{τ′}X^{1/4}`, `‖avgErr‖ ≤ 2N^{τ′}X`, loops `2^{k-1} ≤ 32`, `K₀ = 1`; (`Kell*`): `kellStarEv` at `δ = 1/8`, `Λ_K = 𝔡⁻¹`, `τ_K = ε/2`, `s = 0` | `·det`, `·Kbound`, `·kell` | ok |

## (b) Script output

Commit `b502f4e` on `t/T2193` (`date -u` at the commit: Mon Oct  5 19:02:55 UTC 2026); `git diff --name-only main...t/T2193` lists exactly the three sole writable files.
```
$ git diff --stat main...t/T2193
 RBM3D/Induction/LemDecCalEPrec.lean | 1704 +++++++++++++++++++++++++++++++++++
 RBM3D/Induction/Step5Pins.lean      |    6 +-
 RBM3D/Test/Axioms.lean              |    2 +-
 3 files changed, 1709 insertions(+), 3 deletions(-)
$ lake build RBM3D.Induction.LemDecCalEPrec            (Mon Oct  5 19:07:54 UTC 2026)
Build completed successfully (3844 jobs).
$ lake build RBM3D.Induction.LemDecCalEPrec 2>&1 | grep -c 'LemDecCalEPrec.lean'
0                                                       (no warning, no error of the new file)
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/LemDecCalEPrec.lean | wc -l
0
```
### Axioms (43 public declarations of the new file, extracted by script; `#print axioms` for each)
```
$ lake env lean axioms.lean     (one `#print axioms RBM.Gauss.Sizes.<name>` per public name)
exit=0  lines=43  standard-only=43     (standard-only = lines ending `[propext, Classical.choice, Quot.sound]`)
'RBM.Gauss.Sizes.stLemDecCalE_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### Target 3 (endpoint) and target 1 (pin), extracted by script
```
$ grep -n "^theorem stLemDecCalE_holds" RBM3D/Induction/LemDecCalEPrec.lean
1550:theorem stLemDecCalE_holds (d : ℕ) : STLemDecCalE d := by
$ #check @RBM.Gauss.Sizes.stLemDecCalE_holds
RBM.Gauss.Sizes.stLemDecCalE_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STLemDecCalE d
$ git diff -U0 main...t/T2193 -- RBM3D/Induction/Step5Pins.lean          (hunks at `:156` and `:163`; `STLemDecCalE`, `inst_lemDecCalE` untouched)
-for `D` with `W^D ≥ N`: the three bounds (`res_deccalE_lk`) ...
+for `D` with eventually `(L^dW^{6d})² ≤ W^D` and `J*_{u,D} ≤ W^{1/2}` (DECISIONS §61, §63; paper `W^D ≥ N`, paper-delta T2193a/b): the three bounds (`res_deccalE_lk`) ...
-    ∀ D : ℝ, 0 < D → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
+    (∀ n u D, Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) →
+    ∀ D : ℝ, 0 < D →
+      (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
$ diff <(body of STLemDecCalEConcl, Step5Pins.lean:162-188) <(body of STLemDecCalEConcl_new_pin, docs/tickets/checks/T2193-check.lean)   (27 lines each, `def` line stripped)
BODY IDENTICAL (diff exit 0)
```
### Compiled nonempty instances (same file, `section Instances`, `sz0`, `z0`, `sInst`, `tInst`; `d = 3`)
```
$ grep -n "^example\|^theorem lemDecCalEPrec_inst" RBM3D/Induction/LemDecCalEPrec.lean
1672:theorem lemDecCalEPrec_inst_floor (n : ℕ) :        (L³W¹⁸)² ≤ W⁴² at sz0, every n (target 1's floor; `sz0_L_le_W`)
1683:theorem lemDecCalEPrec_inst_Jst :                   Jst ≡ 1: `1 ≤ 1` and `1 ≤ W^{1/2}` at sz0, every n (target 1's two premises)
1694:example := inst_lemDecCalE (stLemDecCalE_holds 3) 1 one_pos
1698:example (h : STLemDecCalEConcl sz0 (STflowE z0) sInst tInst) :=
          h (fun _ _ _ => 1) lemDecCalEPrec_inst_Jst.1 lemDecCalEPrec_inst_Jst.2 42 (by norm_num) (Eventually.of_forall lemDecCalEPrec_inst_floor)
$ #check (inst_lemDecCalE (stLemDecCalE_holds 3) 1 one_pos)
 : InstIng5Concl (fun {d} sz E s t => sz.STLemDecCalEConcl E s t) sz0 z0 sInst tInst 1
```
Every deterministic hypothesis is discharged (`3 ≤ 3`, flow `z0`, `0 ≤ s < t ≤ lemT`, `sz0_reg5III`, `D = 42`, `Jst ≡ 1`, the floor); the stochastic pins `STKbound … STLKU` of `InstIng5Concl` and the `Prec` premise on `STLK2` stay hypotheses (other gates' pins). Nondegenerate: `N_1 = 2^39`, `L = 8`, `W = 1024`, `(1-1/16)⁻¹ = 16/15 ≤ N` and the floor ratio `P²/W⁴² = 2.3e-13` (`ap.py`, `inst.py` of (a)).
### Registry (DECISIONS §16, §20) and the pre-check
```
$ (temp root in the scratch directory, not committed) the 242 `import` lines of RBM3D.lean + `import RBM3D.Induction.LemDecCalEPrec` (after the last import) + `#assert_rbm_axioms`
$ lake env lean precheck.lean          (Mon Oct  5 19:03:13 UTC 2026)    exit=0
axiom audit: 5939 theorems, 2088 definitions, 0 axioms in `RBM` ...  premises found by scanning: 108 (borrowed 1, owed 84, structural 23).
  RBM.Gauss.Sizes.STLocalEntryU: 5 [no certificate]      (the five new lemmas that assume it)
$ git diff -U0 main...t/T2193 -- RBM3D/Test/Axioms.lean
@@ -118,0 +119 @@  +   `RBM.Gauss.Sizes.STLocalEntryU, -- `(Gt_bound_flow)` uniform in `u ∈ [s,t]` ... (T2193, DECISIONS §20 rule: owed)
@@ -176 +176,0 @@  -   `RBM.Gauss.Sizes.STLemDecCalE, -- `lem_dec_calE`; proved internally (DECISIONS §40); S5-01 (T2138, DECISIONS §40: owed)
$ lake build            (worktree; Mon Oct  5 19:06:44-19:06:52 UTC 2026; the first run, 18:55:45-18:57:16, logged 76 built/replayed jobs and the same single failure)
✖ [4002/4003] Building RBM3D                              (the only `✖` line)
error: RBM3D.lean:245:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of ... [RBM.Gauss.Sizes.STLemDecCalE]
```
The root fails only because `RBM3D.lean` does not yet import the new module (the hub adds the import at merge): without it `stLemDecCalE_holds` is not in the environment, so `STLemDecCalE` is an unproved premise with no registry line (deleted, as the ticket asks); with the import (the temp root above) the audit exits 0. The pin change breaks no other module: every job of the full build except the root succeeded, and `STLemDecCalE`, `inst_lemDecCalE` (in `Step5Pins.lean`) compile unchanged.
### Name clash and ports
```
$ for each of the 43 new public names: grep -rnw NAME RBM3D | grep -v LemDecCalEPrec.lean | grep -v Test/Axioms.lean | wc -l
name-clash grep: 43 new public names, 0 hit(s) in RBM3D outside the new file and the registry comment
main worktree hits: 0
```
No port from `RBM1D`/`RBM2D` (no counterpart for the `Prec` layer): RBM1D/RBM2D diff-stat not applicable. Copies of four private RBM3D helpers are cited in the module header: `kellStar_bparam_le` (`Path/KellStar.lean:68`), `lemDecCalEwG_STavgM_eq_avgErr` (`Path/LemDecCalEwG.lean:839`), `lemDecCalE_STKloop_two` (`Path/LemDecCalE.lean:1276`), the tail floor of `LemDecCalELip_Jsharp_rel` (`Induction/LemDecCalELip.lean:1081-1086`).
### `ap.py` (numeric re-check of (a′); `python3 ap.py`)
```
(i)  tau'=min(tau/24,1/(2D)): 6tau'<=tau/4 and D tau'<=1/2 on 36 grid points: ok
(ii) (C) tau''=tau/(m+1), tau''(1+m)=tau for m in {2,3/2,3}: ok
(iii) 2^(k-1) for k=3,4,6: [4, 8, 32] <= 32; (P-e6) sqrt2 N^{tau'/2} <= 32 N^{tau'}; (P-e9) 2 N^{tau'} <= 32 N^{tau'}
(iv) n=0: L=4 W=32 log2 N=21.00  floor (L^3W^18)^2<=W^42 ok; N<=L^3W^18 ok; N^(1/84)=1.189 <= sqrt(W)=5.66; (1-1/16)^-1=16/15<=N ok
(iv) n=1: L=8 W=1024 log2 N=39.00  floor (L^3W^18)^2<=W^42 ok; N<=L^3W^18 ok; N^(1/84)=1.380 <= sqrt(W)=32.00; (1-1/16)^-1=16/15<=N ok
(iv) n=2: L=12 W=7776 log2 N=49.53  floor (L^3W^18)^2<=W^42 ok; N<=L^3W^18 ok; N^(1/84)=1.505 <= sqrt(W)=88.18; (1-1/16)^-1=16/15<=N ok
(iv) n=3: L=16 W=32768 log2 N=57.00  floor (L^3W^18)^2<=W^42 ok; N<=L^3W^18 ok; N^(1/84)=1.601 <= sqrt(W)=181.02; (1-1/16)^-1=16/15<=N ok
(iv) n=4: L=20 W=100000 log2 N=62.79  floor (L^3W^18)^2<=W^42 ok; N<=L^3W^18 ok; N^(1/84)=1.679 <= sqrt(W)=316.23; (1-1/16)^-1=16/15<=N ok
(iv) n=5: L=24 W=248832 log2 N=67.53  floor (L^3W^18)^2<=W^42 ok; N<=L^3W^18 ok; N^(1/84)=1.746 <= sqrt(W)=498.83; (1-1/16)^-1=16/15<=N ok
(v)  floors R1,R2,R3 >= N^-(1+2D) at n in {1,3}, u in {0,1/32,1/16}, D=3 (tail replaced by its floor W^-D): ok
```
### Narrative
- **Proved:** `stLemDecCalE_holds (d : ℕ) : STLemDecCalE d` for the pin after target 1, unconditionally; 43 public declarations, 1704 lines, standard axioms only. Route (d) of Amend 1: (P) `lemDecCalEPrec_prob` + `_goodDet` + `_precPT`: on the per-time good event `lemDecCalE_lk/_wG/_dif` hold at the realized control `J♯`; (N) `lemDecCalEPrec_lift` (T2198's `LemDecCalELip_lift`, `_ELKLK`, `_EGt`, `_ee`, `_Jsharp_rel`, `_relcont`), the fourth conclusion re-indexed by `StochDomAt.precomp_param`; (C) `lemDecCalEPrec_combine`. No uniform `(P-e7/8)` is stated.
- **Target 1:** the new body equals the check file's `STLemDecCalEConcl_new_pin` (script diff above). Deviation from the ticket text "lines 156, 162, 163 (one inserted line at 162)": I used the check file's line breaks (line 163 becomes three lines), so the script diff is empty; the content is the ticket's (premise `Jst ≤ W^{1/2}`, floor `(L^dW^{6d})² ≤ W^D`, docstring phrase of `:156`).
- **Hypotheses of `STIngR5` used:** `STFlow` (through `v3_premises_of_stFlow`, `Admissible`, `WO`, `Bandwidth`), `STReg5III`, `STStep2Concl.1` (`STLocalEntryU`) and `.2.1` (`STAvgU`), `STLmaxU`, `s ≥ 0`, `t ≤ lemT`; the pin's premises `Jst ≥ 1`, `Jst ≤ W^{1/2}`, the floor, and the `Prec` hypothesis on `STLK2`. Not used: `STKbound`, `STKward`, `STLK s`, `STDecay s`, `STDecayStrong s`, `STConStInd`, `STStep1Loop`, `STLKU`, `STGdecayW`.
- **Per-time `(P-e7/8)`:** `lemDecCalEPrec_gij`: `gbEXPV3` at `(κ/2, 𝔠, 𝔡, ε/2)` and `gijGEXPTSwap_giiGEXPT_of_V3`, with `AsGMcPT` at `c = 𝔡` from `STLocalEntryU` (`lemDecCalEPrec_asGMcPT`: `STWB ≤ 2 W^{-2𝔡}` by `lam_sq_mul_pow_ge`). Nothing about `gexRHS` is lifted in `u`.
- **Loss:** `Λ = 32 N^{τ′}`, `K₀ = 1`; the loss of the three lemmas is `≤ N^{τ/2}` eventually for `6τ′ ≤ τ/4` (`lemDecCalEPrec_RA`: `A (1+6x)^k e^{8x^{3/4}} ≤ e^{cx}` eventually, `x = log N`); the threshold in `n` is astronomically large (as in (a)), no instance needs it.
- **Registry:** the owed line `STLemDecCalE` is deleted. The pre-check then reported the unregistered premise `STLocalEntryU` (assumed by five new lemmas, proved nowhere); it is registered as owed next to `STAvgU` (§20 rule), and the pre-check exits 0. Side effect, not touched: `lemDecCalEPrec_asGMcPT` concludes `AsGMcPT`, so the registry line of `AsGMcPT` (owed) now appears among the "registered premises carry nothing yet" of the pre-check output.
- **Order, stated as it happened:** the Lean was written and compiled before section (a′) was written (the amendment asks for (a′) first); every line of (a′) is a statement about compiled lemmas or `ap.py`, not a prediction.
- **Names:** every helper is `private` or carries the file-stem prefix `lemDecCalEPrec_`; the only other public name is the pinned `stLemDecCalE_holds`; no pinned or merged signature changed.

## (c) Verified Mathlib names used
(each name below was resolved by `ResolveName.resolveGlobalName` in the file's own `open` context, script `modof.lean`: 142 lemma-like names of the 163 non-RBM3D names that occur in the file; the full list grouped by module is `mathlib_names.txt` in the scratch directory)
Bool.false, Bool.true, Classical.not_not, Complex.norm_natCast, Complex.re_le_norm, ENNReal.ofReal, ENNReal.ofReal_le_ofReal, ENNReal.ofReal_mul, ENNReal.ofReal_natCast,
ENNReal.ofReal_ofNat, Filter.Eventually.of_forall, Filter.atTop, Filter.eventually_ge_atTop, Finset.card_univ, Finset.mem_univ, Finset.single_le_sum, Finset.sum_const,
Finset.sum_le_sum, Finset.sum_nonneg, Fintype.card_fin, Fintype.card_fun, Fintype.card_prod, Fintype.card_subtype_le, HNot.hnot, List.ofFn_succ, List.ofFn_zero,
List.prod_cons, List.prod_nil, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_smul, Matrix.trace_sub, Max.max, MeasureTheory.measure_iUnion_fintype_le,
MeasureTheory.measure_mono, MeasureTheory.measure_union_le, Min.min, Nat.cast_mul, Nat.cast_nonneg, Nat.factorial_pos, Nat.le_mul_of_pos_left, Nat.mul_le_mul,
Nat.pow_le_pow_left, Real.add_one_le_exp, Real.exp_add, Real.exp_le_exp, Real.exp_pos, Real.log_exp, Real.log_le_log, Real.log_nonneg, Real.log_pow, Real.mul_rpow,
Real.mul_self_sqrt, Real.one_le_rpow, Real.pow_div_factorial_le_exp, Real.rpow_add, Real.rpow_def_of_pos, Real.rpow_le_one, Real.rpow_le_rpow,
Real.rpow_le_rpow_of_exponent_ge, Real.rpow_le_rpow_of_exponent_le, Real.rpow_le_rpow_of_nonpos, Real.rpow_mul, Real.rpow_natCast, Real.rpow_neg, Real.rpow_neg_one,
Real.rpow_nonneg, Real.rpow_one, Real.rpow_pos_of_pos, Real.rpow_two, Real.sqrt_le_one, Real.sqrt_nonneg, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_union, abs_le,
abs_nonneg, abs_norm_sub_norm_le, abs_of_pos, add_le_add, add_nonneg, by_contra, div_eq_mul_inv, div_le_iff₀, div_le_one, half_pos, inv_anti₀, inv_le_iff_one_le_mul₀',
inv_le_one_of_one_le₀, inv_nonneg, inv_pos, le_max_left, le_max_right, le_of_eq, le_rfl, le_self_pow₀, le_trans, lt_min, lt_of_lt_of_le, min_le_left, min_le_right,
mul_assoc, mul_comm, mul_inv, mul_le_mul, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_nonneg, mul_one, mul_pos, mul_pow, norm_inv, norm_mul, norm_nonneg,
norm_pow, not_exists, not_le, not_lt, not_or, nsmul_eq_mul, one_le_inv₀, one_le_pow₀, one_mul, one_pos, pow_le_one₀, pow_le_pow_iff_left₀, pow_le_pow_left₀,
pow_le_pow_right₀, pow_lt_pow_left₀, pow_mul, pow_nonneg, pow_pos, pow_succ, sq_nonneg, sub_nonneg, tendsto_rpow_atTop, zero_add, zero_le_one
Verified deprecated in this toolchain (build warnings in the tool log): `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`), tactic `push_neg` (use `push Not`; not used), `show` that changes the goal (`linter.style.show`; use `change`).

## (d) Open issues and paper-delta candidates
- **T2193a** (continues D374, D429): the pin's floor `(L^dW^{6d})² ≤ W^D` (eventually) replaces the paper's `W^D ≥ N` (`3_5:2317`) in the `Prec` statement; harmless downstream (`STPfConcl` is monotone in `D`, `T_{u,D}` decreases in `D`).
- **T2193b**: the added premise `J*_{u,D} ≤ W^{1/2}` (met by the stopping time of `lem:pf_step5`, `J* < W^ε`, `ε < 1/2`); the proof uses it only for `J♯ ≤ N^{τ′}Jst ≤ W` (conjunct `J ≤ W` of `E2Hyp`).
- **T2193c′** (Amend 1): `lem_dec_calE` uniform in `u`: the deterministic lemmas are applied per time at the realized control `J♯`, the three conclusions are net-lifted (§7) and `J♯` is replaced by `Jst` on the event of the hypothesis; `(GijGEX)` is used per time in its one-orientation swapped form (no uniform statement).
- **For S5-10/S5-11:** use `D′ = max(D, D₀)` (the pin holds at every `D` with the eventual floor), supply `Jst ≤ W^{1/2}` from the stopping time; `stLemDecCalE_holds` needs `STLocalEntryU`, `STAvgU`, `STLmaxU` (from `STStep2Concl`, `STIngR5`) and the `Prec` hypothesis on `STLK2`.
- **Open (dispatcher):** (1) the registry line of `AsGMcPT` (see (b) Narrative, "Side effect"); (2) the preflight (a) thresholds and mine are `eventually` statements with astronomically large `n`; (3) no further statement differs from the paper beyond T2193a, b, c′ and the earlier deltas (`N^τ` for `W^τ`, explicit loss, `zdistInf`).
