Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 01:23:25 UTC 2026 (`date -u`)

Scripts (python/mpmath, no Lean): `inst3.py`, `s1rand.py` in the scratchpad `T2436/`. Notation: `N = sz.size n = (WL)^d`, `W = sz.W n`, `B = sz.Bctl n (t n)`, `X = twAvgXmax`, `a = K W^{ε'} B`. `Bctl n t = W^{-d} Bparam d L λ t 0` (`Defs/Sizes.lean:214`, `Defs/Params.lean:36`) `= (W^d(λ²+1−t))⁻¹ + (N(1−t))⁻¹` (`K=0`, `N = W^d L^d`). Frame as in `BATwistAvgProd` (`BA/TwistPins.lean:154`): `3 ≤ d`, `κ, ε, 𝔡 > 0` (so `ε > 0`), `BAFlow`, `0 ≤ t n ≤ BAflowT0 < 1` (`BAflow_T0_bounds`, `BA/Step1Trivial.lean:47`). `K` comes from `BATwistAvgRec` (before `𝔠, sz, z`); `τ, D` are the `PrecL` arguments (`Chain/Carrier.lean:51`).

### (i) Exponent table

| # | quantity | value (functions of `τ, D, d, ε, 𝔡`) | constraint | slack |
|---|---|---|---|---|
| 1 | `p ∈ ℕ` | `p = ⌈(D+4)/τ⌉ ≥ 1` | `pτ ≥ D+4` (row 9) | 0 at `(D+4)/τ ∈ ℕ`, else `>0` |
| 2 | `ε'` | `min(𝔡, dε/2, dτ/2)`, `> 0` | (a) `ε' ≤ 𝔡` (`W^{ε'−2𝔡} ≤ W^{−𝔡}`); (b) `ε'/d ≤ ε/2` (`W^{ε'}N^{−ε} ≤ N^{−ε/2}`); (c) `ε'/d ≤ τ/2` (`W^{ε'} ≤ N^{τ/2}`, row 9) | 0 for the minimizing one |
| 3 | `D'` | `2p+2` (the `D` of `BATwistAvgRecAt`) | `N^{−D'}N^{2p−2}c₀^{−(2p−2)} = c₀^{−(2p−2)}N^{−4}` must be `≤ N^{−2} ≤ c₀⁻²B²` (row 7) | exponent slack 2, and after `2c₀^{−(2p−2)} ≤ N` (eventually) slack 1 |
| 4 | floor `c₀` | `c₀ = (𝔡⁻²+1)⁻¹`: `B ≥ W^{−d}(λ²+1)⁻¹ ≥ c₀/N` (`Sizes.STBctl_ge`, `Induction/ScaleFacts.lean:126`; `W^d ≤ N` since `L ≥ 1`; `λ ≤ 𝔡⁻¹` from `WO`, `Defs/Sizes.lean`) | `B ≥ c₀/N` | exact; `c₀ = 1/101` at `𝔡 = 1/10` |
| 5 | ceiling of `B` | `B ≤ W^{−2𝔡} + 2N^{−ε}`: first term `(W^d λ²)⁻¹ ≤ W^{−2𝔡}` by `Sizes.lam_sq_mul_pow_ge` (`Defs/Sizes.lean:193`, from `WO`); second `(N(1−t))⁻¹ ≤ 2(N Im z_n)⁻¹ ≤ 2N^{−ε}` by `BAExp14a_one_sub_t` (`Graph/BAExp14a.lean:1178`: `Im z_n/2 ≤ 1−t`) and `BAdom` (`N^{−1+ε} ≤ Im z_n`) | needs `ε > 0` | — |
| 6 | absorption `a ≤ 1/2` | `K W^{ε'}B ≤ K(W^{−𝔡} + 2N^{−ε/2}) ≤ K(N^{−𝔠𝔡} + 2N^{−ε/2})` (`W ≥ N^𝔠`, `Bandwidth`; `Sizes.W_rpow_le`, `Defs/Sizes.lean:220`) | `≤ 1/2` eventually (`N → ∞`) | decay rate `min(𝔠𝔡, ε/2)` = `1/60` at `(𝔠,𝔡,ε) = (1/6,1/10,1/10)` |
| 7 | S1 constant | `C' = 2K + √(4pK + c₀⁻²)`; the pin at the maximizer gives `X^{2p} ≤ 2aX^{2p−1} + 4paBX^{2p−2} + 2N^{−D'}` (uses `1−a ≥ 1/2`) | `X ≤ C' W^{ε'}B` | see S1 below |
| 8 | per-pair Markov | `P(N^τB < ‖T‖) ≤ E‖T‖^{2p}/(N^τB)^{2p} ≤ (C'W^{ε'}N^{−τ})^{2p} ≤ C'^{2p}N^{−pτ}` | `W^{ε'} ≤ N^{ε'/d} ≤ N^{τ/2}` (row 2c) | 0 |
| 9 | union and total | `#pairs = L^{2d} ≤ N²` (`W ≥ 1`); `N² C'^{2p} N^{−pτ} ≤ N^{−D}` iff `C'^{2p} ≤ N^{pτ−D−2}`; with `pτ ≥ D+4` it suffices `C'^{2p} ≤ N²` | eventually | exponent slack 2 (absorbs `C'^{2p}`) |
| 10 | integrability | `‖twTr‖^{2p}` integrable at `seqP (sz.withLam 0)`: `twAvgReg_holds` (`BA/TwistAvgA.lean:613`), needs `0 < κ, 0 < ε`, `t ≤ T₀` | — | — |

**S1 case split (exponents).** Take `(c₁,c₂)` with `twAvgX c₁ c₂ = X` (`Finset.exists_mem_eq_sup'`); `X ≥ 0`. Pin at that pair with `a ≤ 1/2`: `X^{2p}(1−a) ≤ aX^{2p−1} + 2paBX^{2p−2} + N^{−D'}`, so `X^{2p} ≤ 2aX^{2p−1} + 4paBX^{2p−2} + 2N^{−D'}`.
- Case 1, `X ≤ B`: `X ≤ B ≤ C'W^{ε'}B` (`W ≥ 1`, `C' ≥ 1`).
- Case 2, `X > B ≥ c₀/N`: divide by `X^{2p−2} > 0`: `X² ≤ 2aX + 4paB + 2N^{−D'}X^{2−2p}` with `X^{2−2p} ≤ B^{2−2p} ≤ (N/c₀)^{2p−2}` (as `2−2p ≤ 0`). Third term `≤ 2c₀^{−(2p−2)}N^{−D'+2p−2} = 2c₀^{−(2p−2)}N^{−4} ≤ N^{−3}` (eventually `2c₀^{−(2p−2)} ≤ N`) `≤ N^{−2} ≤ c₀^{−2}B²`. Hence `X² ≤ αX + β`, `α = 2KW^{ε'}B`, `β ≤ (4pK + c₀⁻²)W^{ε'}B²`; so `X ≤ α + √β ≤ C'W^{ε'}B` (`W^{ε'/2} ≤ W^{ε'}`).
- No smallness of `X` or `W^{ε'}B` beyond `a ≤ 1/2` is used; `p = 1` is allowed (`X^{2p−2} = 1`).

**Lemmas.** `Sizes.lam_sq_mul_pow_ge`, `Sizes.W_rpow_le`, `Sizes.STBctl_ge`, `Sizes.STBctl_pos` (`B > 0`, `t < 1`), `BAExp14a_one_sub_t`, `BAflow_T0_bounds`, `Sizes.tendsto_size`, `Admissible` fields (`Bandwidth`, `WO`, `BAdom`) from `BAFlow`. Markov: Mathlib `mul_meas_ge_le_integral_of_nonneg` (`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1162`: `ε * μ.real {x | ε ≤ f x} ≤ ∫ f`; `f = ‖twTr‖^{2p}`, `ε = (N^τB)^{2p}`, `f ≥ 0`, integrable by row 10; the bad event `N^τB < ‖T‖` is contained in `{ε ≤ f}`). Union: `measure_iUnion_fintype_le` (`Mathlib/MeasureTheory/OuterMeasure/Basic.lean:84`) over `Zd d L × Zd d L` (the `u` of `badSetAt`, `Defs/StochDomAt.lean:52`). The measure is a probability measure (instance `isProbabilityMeasure_seqP`, `Gauss/FineModel.lean:171`).

**No net, no extra premise.** The premises of `BATwistAvgProd` and `BATwistAvgRec` coincide (`TwistPins.lean:154-155`, `TwistAvgA.lean:147-150`): `LWAvgLawgL`, `STLmaxgL` and the flow data; the proof of target 1 passes them to `BATwistAvgRec` and uses the proved facts above and `twAvgReg_holds`; no `STLKgL`, no `BAGbEXP*` and no `N^{−C}`-net in `u` appear (the pin is per `τ`, the union is over the finite set of pairs).

### (ii) One concrete nondegenerate instance

Datum of `BA/TwistAvgA2.lean` §7: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `λ = (2(n+1))^{−6}`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`), `t ≡ 1/2`, `1/2 < BAflowT0 sz0 zSeq n` (`half_lt_t0`, `FlowPins.lean:1254`), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`. Test `(τ, D) = (1/2, 1)`: `p = 10`, `ε' = min(1/10, 3/20, 3/4) = 1/10`, `D' = 22`, `pτ = 5 = D+4`. `K` (an existential of the pin) is run at `1`, `16.6` (`C_M + 1` for the numerical `C_M = 15.6`, `T2427-prove.md` (a) row 7) and `4.943e15 + 1` (the proved `C_M`, `T2427-prove.md` row 8, quoted, not re-derived here).
```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2436 && python3 inst3.py | sed -n 1,26p
c0=(dd^-2+1)^-1 = 0.00990099 ; 1/c0^2 = 10201.0
n=0: L,W,lam,N = 4 32 0.015625 2097152  Bctl(1/2)= 6.1959e-5

--- tau=0.5 D=1 K=1.0: p=10 eps'=0.1 D'=22 C'=103.198  p*tau=5.0>=D+4=5
  first n with E1x  K W^eps` Bctl(n,1/2) <= 1/2 (exact B at t=1/2) : 0
  first n with E1p  K W^eps` (W^-2dd + 2N^-eps) <= 1/2 (bound valid for all t<=T0) : 3
  first n with E2   2 c0^-(2p-2) <= N : 46
  first n with E3   C`^(2p) <= N^2 : 5
  n* = 46
  at n*: N=2.627e+36 W=7.339e+9 Bctl(1/2)=5.06e-30 a=K W^eps` B=4.905e-29
   B>=c0/N: True | lam^2 W^d>=W^(2dd): True | W^d<=N: True | W^eps`<=N^(eps`/d)<=N^(tau/2): True
   max-recursion solved with equality: X*=9.9129e-29; X*>B: True; S1 bound C` W^eps` B=5.0623e-27; X*<=bound: True; X*/(W^eps` B)=2.0208
   case-2 third term 2N^-D' X^(2-2p) <= 2 N^-D' B^(2-2p) = 2.514e-274 <= c0^-2 B^2 = 2.611e-55: True
   union*Markov: log10[N^2 (C` W^eps`/N^tau)^(2p)]=-231.35 <= log10 N^-D=-36.4194: True

--- tau=0.5 D=1 K=16.6: p=10 eps'=0.1 D'=22 C'=137.435  p*tau=5.0>=D+4=5
  first n with E1x  K W^eps` Bctl(n,1/2) <= 1/2 (exact B at t=1/2) : 0
  first n with E1p  K W^eps` (W^-2dd + 2N^-eps) <= 1/2 (bound valid for all t<=T0) : 557
  first n with E2   2 c0^-(2p-2) <= N : 46
  first n with E3   C`^(2p) <= N^2 : 6
  n* = 557
  at n*: N=5.768e+55 W=1.731e+15 Bctl(1/2)=3.855e-46 a=K W^eps` B=2.138e-43
   B>=c0/N: True | lam^2 W^d>=W^(2dd): True | W^d<=N: True | W^eps`<=N^(eps`/d)<=N^(tau/2): True
   max-recursion solved with equality: X*=2.2125e-43; X*>B: True; S1 bound C` W^eps` B=1.7701e-42; X*<=bound: True; X*/(W^eps` B)=17.179
   case-2 third term 2N^-D' X^(2-2p) <= 2 N^-D' B^(2-2p) = 1.021e-409 <= c0^-2 B^2 = 1.516e-87: True
   union*Markov: log10[N^2 (C` W^eps`/N^tau)^(2p)]=-372.85 <= log10 N^-D=-55.761: True
```
Thresholds of all six `(τ, D, K)` blocks (all other checks in `inst3.out` are `True`), from the same command:
```
$ python3 inst3.py | grep -E "^---|n\* =|first n with E[123]"
--- tau=0.5 D=1 K=1.0: p=10 eps'=0.1 D'=22 C'=103.198  p*tau=5.0>=D+4=5
  first n with E1x  K W^eps` Bctl(n,1/2) <= 1/2 (exact B at t=1/2) : 0
  first n with E1p  K W^eps` (W^-2dd + 2N^-eps) <= 1/2 (bound valid for all t<=T0) : 3
  first n with E2   2 c0^-(2p-2) <= N : 46
  first n with E3   C`^(2p) <= N^2 : 5
  n* = 46
--- tau=0.5 D=1 K=16.6: p=10 eps'=0.1 D'=22 C'=137.435  p*tau=5.0>=D+4=5
  first n with E1x  K W^eps` Bctl(n,1/2) <= 1/2 (exact B at t=1/2) : 0
  first n with E1p  K W^eps` (W^-2dd + 2N^-eps) <= 1/2 (bound valid for all t<=T0) : 557
  first n with E2   2 c0^-(2p-2) <= N : 46
  first n with E3   C`^(2p) <= N^2 : 6
  n* = 557
--- tau=0.5 D=1 K=4.943e+15: p=10 eps'=0.1 D'=22 C'=9.886e+15  p*tau=5.0>=D+4=5
  first n with E1x  K W^eps` Bctl(n,1/2) <= 1/2 (exact B at t=1/2) : 6
  first n with E1p  K W^eps` (W^-2dd + 2N^-eps) <= 1/2 (bound valid for all t<=T0) : 48866498000000019772000004061902
  first n with E2   2 c0^-(2p-2) <= N : 46
  first n with E3   C`^(2p) <= N^2 : 342705368
  n* = 48866498000000019772000004061902
--- tau=0.1 D=3 K=1.0: p=70 eps'=0.1 D'=142 C'=104.377  p*tau=7.0>=D+4=7
  first n with E1x  K W^eps` Bctl(n,1/2) <= 1/2 (exact B at t=1/2) : 0
  first n with E1p  K W^eps` (W^-2dd + 2N^-eps) <= 1/2 (bound valid for all t<=T0) : 3
  first n with E2   2 c0^-(2p-2) <= N : 1076430742831536
  first n with E3   C`^(2p) <= N^2 : 31544539
  n* = 1076430742831536
--- tau=0.1 D=3 K=16.6: p=70 eps'=0.1 D'=142 C'=155.056  p*tau=7.0>=D+4=7
  first n with E1x  K W^eps` Bctl(n,1/2) <= 1/2 (exact B at t=1/2) : 0
  first n with E1p  K W^eps` (W^-2dd + 2N^-eps) <= 1/2 (bound valid for all t<=T0) : 557
  first n with E2   2 c0^-(2p-2) <= N : 1076430742831536
  first n with E3   C`^(2p) <= N^2 : 147017886
  n* = 1076430742831536
--- tau=0.1 D=3 K=4.943e+15: p=70 eps'=0.1 D'=142 C'=9.886e+15  p*tau=7.0>=D+4=7
  first n with E1x  K W^eps` Bctl(n,1/2) <= 1/2 (exact B at t=1/2) : 6
  first n with E1p  K W^eps` (W^-2dd + 2N^-eps) <= 1/2 (bound valid for all t<=T0) : 48866498000000019772000004061902
  first n with E2   2 c0^-(2p-2) <= N : 1076430742831536
  first n with E3   C`^(2p) <= N^2 : 71065113187072551281173371901259470199528754100332328416891447
  n* = 71065113187072551281173371901259470199528754100332328416891447
```
Reading: at `t = 1/2` the absorption `a ≤ 1/2` holds already at `n = 0` for `K ≤ 5706` (`a = K·8.762e-5` at `n = 0`: `W^{ε'}B = 32^{0.1}·6.196e-5`); `Bctl_n = 6.2e-5, 1.9e-9, 4.3e-12, 5.7e-14` at `n = 0..3` (`~ 2W^{−3}`), floor `Bctl_n ≥ c₀/N_n`. The thresholds `n*` are for the eventual conclusion (`∀ᶠ n`), not for any hypothesis: every hypothesis of targets 1-3 holds at `n = 0` (the datum is merged: `flow_sz0`, `half_lt_t0`). Constants of the pin (`K`, `C_M`) make `n*` large; this is a constant, not a degeneracy.

Randomised check of the S1 deduction (algebra only: random `K, w = W^{ε'} ≥ 1, B ≥ c₀/N, N ∈ [10^{40},10^{60}], p ∈ {1,2,3,10}`, `D' = 2p+2`, `2c₀^{−(2p−2)} ≤ N`, `a ≤ 1/2`; `X*` = largest `X` with the maximizer recursion):
```
$ python3 s1rand.py
trials=3000  violations of X<=C` W^eps` B: 0  max X*/(C` W^eps` B)=0.861  trials with X*>B (case 2): 2999
```
**External hypotheses (`LWAvgLawgL`, `STLmaxgL`) — limit computation.** Both are asymptotic pins of other gates (stay hypotheses of the instance). Concrete values along `sz0`, `t = 1/2` (`python3` one-liner on `Bparam`): `n = 0..3`: `Bctl = 6.1959e-5, 1.8663e-9, 4.2561e-12, 5.6857e-14`; `1/N = 4.768e-7, 1.819e-12, 1.231e-15, 6.939e-18`; `W^{ε'}Bctl = 8.762e-5, 3.733e-9, 1.043e-11, 1.608e-13`. So `Bctl_n → 0` polynomially in `W` (`~ 2W^{−3}`, no contradiction with `|𝓛¹−m| ≺ Bctl` since `Bctl ≥ N^{−1}` is the ≺-floor), the floor `Bctl ≥ c₀/N` used in S1 holds, and the consumer's `K W^{ε'}Bctl ≤ 1/2` tends to `0`. (Matches the values of `T2427-prove.md` (a) `inst.out`: `6.2e-5, 1.9e-9, 4.3e-12, 5.7e-14`.)

### Verdicts
- **Target 1** (`baTwistAvgProd_of_rec : T2427_TL1b`): **PASS.** Constants: rows 1-3; absorption row 6; S1 split rows 4, 7 and the case split; Markov and union rows 8-9. Every exponent closes with slack `≥ 0` (rows 1-2 are equalities for the extremal choices; row 9 has slack 2).
- **Target 2** (`baTwistAvgProd_holds d` from target 1 and `baTwistAvgRec_holds`): **PASS.** Same frame and premises (`TwistPins.lean:154`, `TwistAvgA.lean:147`); `3 ≤ d` is a hypothesis of both.
- **Target 3** (instance at `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`, hypotheses `LWAvgLawgL`, `STLmaxgL` as in `TwistAvgA2.lean:1167`): **PASS** at the data of (ii).
- **Target 4** (registry: none): no mathematics.
- Lines (v): own estimate, basis `BA/TwistAvgA2.lean` (1228 lines, instance §7 about 100 lines): `Bctl` ceiling and floor at `BAFlow` ≈ 110, real-algebra S1 lemma ≈ 90, per-`n` step (maximizer, recursion, S1, bound `X ≤ C'W^{ε'}B`) ≈ 150, Markov per pair ≈ 70, union and card `L^{2d} ≤ N²` ≈ 70, assembly (`τ, D, p, ε', D'`, eventually, `filter_upwards`) ≈ 120, `baTwistAvgProd_holds` ≈ 10, instance ≈ 40, header/statements ≈ 40: **≈ 700** (range 500-1,000, stop line 1,500).
- Observation: the ticket's `D' = 2p+2` closes with the eventual absorption `2c₀^{−(2p−2)} ≤ N` (row 3), which costs a threshold `n*` that grows like `c₀^{−(2p−2)}` (`n* ≈ 1e15` at `p = 70`); this is a constant of an eventual statement (alternative `D'` does not remove it).

## (a′) Preflight corrections — Mon Oct 12 03:28:14 UTC 2026 (`date -u`)
No verdict changes (targets 1-4 stay PASS). Three differences between (a) and the proof as built:
1. Floor: `B ≥ N⁻¹` holds with `c₀ = 1` (`cont_inv_size_le_Bctl`, `Induction/ContinuityNet.lean:701`). So row 4's `c₀ = (𝔡⁻²+1)⁻¹` and the eventual condition `2c₀^{−(2p−2)} ≤ N` (rows 3, 7 and the last observation of (a)) are not used: `N^{−D'} = N^{−(2p+2)} ≤ N^{−2p} ≤ B^{2p}` for `N ≥ 1`.
2. `ε'` (row 2) is `d·min(c, τ/2)`, `c = min(2𝔡𝔠, ε)/2`, not `min(𝔡, dε/2, dτ/2)`: the ceiling is proved as `B ≤ N^{−2𝔡𝔠} + 2N^{−ε}`, then `W^{ε'} ≤ N^{ε'/d} ≤ N^c`. `ε'` depends on `𝔠`; allowed, `BATwistAvgRecAt` quantifies `ε'` after `K, 𝔠, sz, z`.
3. S1 without square root: `C' = (4p+2)K+2` (row 7: `2K + √(4pK + c₀⁻²)`), by contradiction from `X² ≤ 2K(wB)X + (4pKw+2)B²`.

## (b) Script output and narrative (stage 1b, `prover-hard`, branch `t/T2436`; times from `date -u` or the tool log)
**Constants (1a (i)) and the S1 split.** `τ, D > 0`; `K` from `BATwistAvgRec`; `c = min(2𝔡𝔠, ε)/2`, `p = ⌈(D+4)/τ⌉`, `ε' = d·min(c, τ/2)`, `D' = 2p+2`, `C' = (4p+2)K+2`; `w = W^{ε'}`, `B = Bctl n (t n)`, `N = sz.size n`. Eventually in `n`: (E1) `K w B ≤ 1/2` (`TwistAvgB_absorb`: `B ≤ N^{−2𝔡𝔠} + 2N^{−ε} ≤ 3N^{−2c}`, `w ≤ N^c`, `3K N^{−c} ≤ 1/2`); (E2) `C'^{2p} ≤ N²`; (E3) `N ≥ 1`. For all `n`: `B ≥ N⁻¹`.
S1 at the maximizer `X = twAvgXmax` (`TwistAvgB_Xmax_le`, `TwistAvgB_S1`): `X^{2p} ≤ a(X^{2p−1} + X·X^{2p−1}) + 2p·a·B·X^{2p−2} + N^{−D'}`, `a = K w B ≤ 1/2`. Case `X ≤ B`: `X ≤ B ≤ C' w B`. Case `X > B`: `N^{−D'} ≤ B^{2p} ≤ B² X^{2p−2}`, divide by `X^{2p−2}`: `X² ≤ 2K·wB·X + (4pKw+2)B²`; `X > C' wB` gives `X(X − 2KwB) > C' wB·(4pK+2)wB ≥ (4pKw+2)B²`, a contradiction. So `X ≤ C' w B`.
Markov per pair (`TwistAvgB_markov`, `TwistAvgB_expo`): `μ{N^τ B < ‖twTr c₁ c₂‖} ≤ (C' w/N^τ)^{2p} ≤ C'^{2p}N^{−pτ} ≤ N^{−(D+2)}` (`w ≤ N^{τ/2}`, `pτ ≥ D+4`, (E2)); union over `L^{2d} ≤ N²` pairs (`TwistAvgB_union`, `TwistAvgB_card_le`): `≤ N^{−D}`. Integrability from `twAvgReg_holds`. No net; no `STLKgL`/`BAGbEXP*`: the premises are those of `BATwistAvgRecAt` (`LWAvgLawgL`, `STLmaxgL`).
**Lines:** 504 (`wc -l`) against the stop line 1,500 and the 1a estimate ≈ 700 (range 500-1,000); no section commit exceeded the stop size.
```
$ lake build RBM3D.BA.TwistAvgB 2>&1 | tail -1
Build completed successfully (4008 jobs).
$ lake build   # RBM3D.lean with one temporary line `import RBM3D.BA.TwistAvgB` (reverted afterwards; `git status --short` empty); `date -u` before: 03:23:37, after (build finished): 03:24:37 UTC
Build completed successfully (4251 jobs).   [`RBM3D.lean` ends with `#assert_rbm_axioms`]
$ lake env lean axioms.lean   # import RBM3D.BA.TwistAvgB; #print axioms of the two public theorems
'RBM.BA.baTwistAvgProd_of_rec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistAvgProd_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2436-check.lean > /dev/null 2>&1; echo $?     # the dispatcher's check file
0
```
**Targets** (extracted by `grep`; the pinned statements, no extra hypotheses; `BATwistAvgProd` is `BA/TwistPins.lean:154`):
```
$ grep -n -A1 "^theorem baTwistAvgProd" RBM3D/BA/TwistAvgB.lean | grep -v '^--'; grep -n "^def T2427_TL1b" RBM3D/BA/TwistAvgA2.lean
444:theorem baTwistAvgProd_of_rec : T2427_TL1b := by
445-  intro d hRec hd κ ε 𝔡 hκ hε h𝔡
451:theorem baTwistAvgProd_holds (d : ℕ) : BATwistAvgProd d :=
452-  baTwistAvgProd_of_rec d (baTwistAvgRec_holds d)
1219:def T2427_TL1b : Prop := ∀ d, BATwistAvgRec d → BATwistAvgProd d
```
**Instance** (§7 of the file, lines 464-504; `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`, `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`; `hA = LWAvgLawgL`, `hM = STLmaxgL` are other gates' pins, every deterministic hypothesis is discharged):
```
$ grep -n "^example" RBM3D/BA/TwistAvgB.lean | cut -c1-90
464:example : T2427_TL1b := baTwistAvgProd_of_rec
465:example : ∀ d, BATwistAvgProd d := baTwistAvgProd_holds
468:example (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz s
474:example (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz s
483:example (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz s
$ sed -n 470,475p RBM3D/BA/TwistAvgB.lean   # the instance of target 2 at the datum
/-- Target 2 at the datum: `baTwistAvgProd_holds 3` at `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`; `LWAvgLawgL`, `STLmaxgL` are other gates' pins. -/
example (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    BATwistAvgLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) :=
  baTwistAvgProd_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hA hM
```
The examples at lines 464-465 are `example : T2427_TL1b := baTwistAvgProd_of_rec` and `example : ∀ d, BATwistAvgProd d := baTwistAvgProd_holds`; line 474 applies `baTwistAvgRec_holds 3` to the same datum; line 483 is a non-vacuity check of the conclusion at `(τ, D) = (1/2, 1)`: eventually in `n` some `ω` has `‖twTr c₁ c₂‖ ≤ N^{1/2} B` for all pairs (the bad set has measure `≤ N⁻¹ < 1`).
```
$ grep -rn --include='*.lean' -e baTwistAvgProd_of_rec -e baTwistAvgProd_holds -e TwistAvgB_ RBM3D RBM3D.lean | grep -v '^RBM3D/BA/TwistAvgB.lean' | wc -l
0
$ grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/BA/TwistAvgB.lean
0
$ git diff --stat main...t/T2436
 RBM3D/BA/TwistAvgB.lean | 504 ++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 504 insertions(+)
```
Public names: `baTwistAvgProd_of_rec`, `baTwistAvgProd_holds` (pinned). All other declarations are `private` with the stem `TwistAvgB_` (CLAUDE.md §3 (E)). `RBM3D.lean` is not in the branch diff (the hub adds the import at merge, §3 (A) step 4). Registry: none; the owed line `BATwistAvgLaw` in `RBM3D/Test/Axioms.lean` is untouched.
**Ports:** none from RBM1D/RBM2D. `TwistAvgB_Bctl_le` is adapted from the RBM3D lemma `lwN_Bctl_le` (`Graph/LWTermExpN.lean:225`, last change in commit `84cd789`) from `STFlow` to `BAFlow` (`BAExp14a_one_sub_t` for `1 − t`).

## (c) Verified Mathlib names (`#check`-level: the file compiles with each; file:line from `grep`)
- `mul_meas_ge_le_integral_of_nonneg` (`MeasureTheory/Integral/Bochner/Basic.lean:1162`), `ofReal_measureReal` (`MeasureTheory/Measure/Real.lean:65`), `measure_iUnion_fintype_le` (`MeasureTheory/OuterMeasure/Basic.lean:84`)
- `Finset.exists_mem_eq_sup'` (`Data/Finset/Lattice/Fold.lean:764`), `Nat.ceil_pos` (`Algebra/Order/Floor/Defs.lean:161`), `Nat.le_ceil` (`Algebra/Order/Floor/Semiring.lean:178`), `ENNReal.one_le_ofReal` (`Basic/ENNReal/Real.lean:216`)
- `Real.rpow_le_rpow_of_exponent_le` (`Analysis/SpecialFunctions/Pow/Real.lean:617`), `Real.rpow_le_rpow_of_nonpos` (`:565`), `Real.one_le_rpow` (`:678`), `Real.rpow_neg_one` (`:474`), `tendsto_rpow_atTop` (`Pow/Asymptotics.lean:38`)
- `div_le_div₀` (`Algebra/Order/GroupWithZero/Basic.lean:1279`), `le_div_iff₀` (`:1129`), `one_le_inv₀` (`:896`), `inv_anti₀` (`:1221`), `pow_le_pow_left₀` (`:514`), `mul_lt_mul''` (`:101`), `div_le_div_of_nonneg_right` (`:1194`)
- Absent or deprecated: `push_neg` is deprecated in this Mathlib (warning at first compile); the file uses `not_le.mp` and `push Not`.
- RBM3D names used (file:line): `cont_inv_size_le_Bctl` (`Induction/ContinuityNet.lean:701`), `STBctl_pos` (`Induction/ScaleFacts.lean:64`), `Sizes.lam_sq_mul_pow_ge` (`Defs/Sizes.lean:193`), `Sizes.W_rpow_le` (`:220`), `Sizes.tendsto_size` (`Defs/StochDomAt.lean:735`), `card_Zd` (`Defs/Lattice.lean:67`), `BAExp14a_one_sub_t` (`Graph/BAExp14a.lean:1178`), `BAflow_T0_bounds` (`BA/Step1Trivial.lean:47`), `ba_G_data` (`BA/GreenLDE.lean:55`), `twAvgReg_holds` (`BA/TwistAvgA.lean:613`), `baTwistAvgRec_holds` (`BA/TwistAvgA2.lean:1040`).

## (d) Open issues and paper-delta candidates
- **T2436a** (S1, T.7 Step 5): the Lean S1 uses `B ≥ N⁻¹` and `D' = 2p+2` (`N^{−D'} ≤ B^{2p}`), constant `C' = (4p+2)K+2` and no additive `N^{−D/2}` term; the paper's `(C.1)` has `(2C_M + 2√(pC_M))W^εW^{−d}B + 2N^{−D/2}` (`TP:90`; supervisor 0652 S1 already records the `X ≥ 1` gap). Constants only.
- **T2436b** (T.7 Step 6): the Lean Step 6 is per `τ` and per ordered pair `(c₁, c₂)` (one charge, as `BATwistAvgLaw`): Markov at the level `N^τ B` and the union over `L^{2d} ≤ N²` pairs; no `N^{−C}`-net in `u` and no sum over the two signs (the uniform-in-`u` lift is the consumer's, T2413 §5). The conclusion is the `≺` of `PrecL` at the scale `N` (`N^τ B`, probability `≥ 1 − N^{−D}`), not `W^{2ε}W^{−d}B` with `W^{−D}`; `ε'` is `d·min(c, τ/2)`, `c = min(2𝔡𝔠, ε)/2`, not the paper's `ε < 𝔡/2`.
- No obstruction, no hypothesis added, no signature changed. The preflight observation on `n*` growing like `c₀^{−(2p−2)}` does not apply to this proof (a′ item 1): the eventual conditions are (E1)-(E3).
