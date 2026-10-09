Prover model: claude-sonnet-5-5
## (a) Math preflight — Fri Oct 9 02:13:33 UTC 2026
Scripts (python, no Lean) in `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2359`: `kw2.py`, `sz.py`, `priv2.py`, `pre.py` (output `pre.out`).
Notation: `ρ'` = the shift radius (`2ρ'` in `hcmp`), `R(s) = W^{-d} tailT(s) / sfT(s)²`, `m = min(r,ℓ)`, `𝖳 = sfT`.

### (i) Exponent table
| # | item | value | constraint | slack |
|---|---|---|---|---|
| 1 | de-privatised keywords `LWMomExp.lean` | 11: chain_nonneg 152, step_aux 310, sys_bound 434, stepFn 710, walk_chain 752, path_ne 835, sysOf_length 846, sysOf_mem 851, pathEdges 862, pathEdges_card 874, prod_split 882; nothing else | each is referenced by the copied segments (10, `kw2.py`) or occurs in the statement of a referenced one (`stepFn` in `walk_chain`) | 0 spare; `_disj`, `path_split`, `walk_last/visit`, `stepFn_eq`, `base`, `marks` stay private |
| 2 | segments copied from `LWMomExp.lean` | tau block 521-581; `TTkBody`…`sys_near` 584-699; `nSolid`, `ordN`, `near_graph`, `near` 918-1024 | `zdistD ↦ zdistInf` in `tau` (521-525), `TTkBody` (`hD`, `x y`), `hstep` (centre `c` and arbitrary `D` with `∀α∈D, |c-α|∞ ≤ ℓ` replace `nearD`), last line of `near_graph`; symmetry `anpKey_zdistInf_neg` (`AnpKey.lean:91`) | generic part 304-516 has no `zdist`: not copied |
| 3 | kernel copies (`PropT.lean`) | ticket: `sfT_pair_le` 788, `prod_sfT_pair_le` 839, `key_T_reduce` 913, `key_T_reduce_absorbed` 1056. **Also needed, not in the ticket: `sfT_TtTt` 644, `sfT_KtKt` 672, `sfT_pair_cases` 690** (`sfT_pair_le:811` calls `sfT_pair_cases`, which uses `zdistD_add_le`) | only triangle (`anpKey_zdistInf_tri` `:101`) and symmetry are used; `sfT_mul_le_TtTt/KtKt`, `wfac_*`, `prod_wfac_le_two`, `PsiT_sq_mul_le`, `keyC` are norm-free (reused) | omission = 85 source lines (`sz.py`) |
| 4 | `C_∞ = 3·keyC∞(k,n)`, `keyC∞ = (√2^k)^n · 4 · d^{k+2} · ballC k`, `k=d-2` | d=3, n=2: 6.50e8 | `D ⊂ ℓ^∞`-ball(c,ℓ) ⊂ `ℓ¹`-ball(c,dℓ) (`zdistD_le_mul_zdistInf`, `Defs/Sizes.lean:122`); `min(r₁,dℓ)+1 ≤ d(min(r_∞,ℓ)+1)`; `1 ≤ dℓ` | `C` depends on `d,n` only; needed C at the instance 0.378 |
| 5 | hypotheses of `EKTTkInf`, `AnpNearInfAt` | `t<1`, `0≤g`, `g² ≤ L²(1-t)`, `1 ≤ ℓ ≤ Λℓ_t` | as merged `EKTTk` (non-strict) | figAux data meets `ℓ ≤ Λℓ_t` with equality (ℓ_t = 1) |
| 6 | class for G2 (corrected) | `Φ_E := (W^{-d} tailW_{ℓ,W,D'})^{1/2}`, `D' = 2D`; (the design's `C₀𝖳(·∧ℓ)+W^{-D'}` needs `zeroMode_le_of_ge` for `LWLoop2`, i.e. regime-1) | (c1) `Φ_E>0`: `tailW_pos` `Defs/Tail.lean:105`. (c2) `hloop` is `LWLoopExp` at `D'` verbatim. (c3) `hW`: `W^{-d} ≤ C₃²Φ_E(0)²`, `C₃² = 1+𝔡^{-2}` (WO `λ ≤ 𝔡⁻¹`, `|1-t| ≤ 1`, `B_{t,0} ≥ (g²+1-t)⁻¹`; same `C₃` as `LWPhiB_psiAll`, `LWPsi.lean:422`). `LWClass` upper bound `≤ W^{-ε₀}` is not used by `lwXiClaim_holds` (only `.1`) | regime-free |
| 7 | `hcmp` | `Φ_E(m)² ≤ Kn² Φ_E(ℓ')²` for `ℓ' ≤ 2ρ'+m`, `Kn² = (2ρ'+1)^{d-2} e^{√(2ρ'/ℓ_t)}`: B-part `s_ℓ+1 ≤ (2ρ'+1)(s_m+1)`, exp-part `sqrt_le_add_sqrt_shift`, floor via `Kn ≥ 1`, `ℓ_t ≥ 1` (`one_le_ellT`) | `Kn ≤ N^{τ/8}`: `N^{τ/16}` each; need `√ρ ≤ (τ/(8√2)) log N = 0.0884τ log N`, hypothesis gives `τ' = τ/12` (slack 6%); `(2ρ+1)^{(d-2)/2}`, `2(2ρ+1)^{2d}` polylog `≤ N^σ` | script D: 0/20000 violations (`tailT` shift is new, probe `:407` is the zero-mode-free `sfT` form) |
| 8 | **(c5) comparison to the target**: `Φ_E(r)² ≤ (1+2^{d-1}) 𝖳(m)² + W^{-d-D'}` | needs `zeroMode_le_of_ge` (`Defs/Tail.lean:119`): `g²/L² ≤ 1-t` and `m ≤ r ≤ L` | regime-1: `max R/(1+2^{d-1}) = 0.434`. **For `1-t < g²/L²`: `R = 1+(g²+1-t)(s+1)^{d-2}/(L^d(1-t))` is unbounded** (script E: `N^{0.17..0.20}` at sz0 n=500, `t=lemT(z)`, `z = iN^{-1+ε}`, vs `N^{2τ}`) | none: link false in regime-2 |
| 9 | (A) chain at general `K>0` | `Φ_B(cr)² ≤ (1+2^{d-1})(2/min(c,1))^{d-2} e^{√(m/ℓ_t)} 𝖳(m)²`; `regA ⇒ m/ℓ_t ≤ K(log W)^{3/2}`; loss `e^{(p/2)√K (log W)^{3/4}}` | `≤ N^{τ'}` iff `log W ≥ (p√K/(2τ'd))^4` (`log N ≥ d log W`); p=2,K=6,τ'=.05,d=3: 7.1e4 | the factor is `e^{-√K(log W)^{3/4}}`, not a constant: `N^{-o(1)}`; `K` enters the threshold only; script F 0/60000 violations, max ratio 0.23 |
| 10 | (A) constants and quantifiers | `LWPhiB_psiAll`: `(C₁,C₂,C₃,Cc) = (2^d, d, √(1+𝔡⁻²), C↦√((C+1)^{d-2}))` depends on `d,𝔡` only (before `ε₀`, `c` in `LWMoment`); `ε₁ = min(ε₀, d c₁/2)`, `c₁ = min(2𝔡𝔠,ε)/2` is instantiated inside, after `𝔠`; `c` from `∃c` of `lwMoment_holds` | `c ≥ 1`: antitone; `c<1`: factor `2/c` | `LWLoop2` for `Φ_B` from `lwN_tailW_le` (`LWTermExpN.lean:121`, all regimes) |
| 11 | `lwTail32` | `log W ≥ (2A/(𝔠c))²`, `A = |a|+|b|` | worst case `log N = log W/𝔠` | equality at threshold (script G); `c>0` free (C4 (c)) |
| 12 | G2 radius | `ρ_n = (log N_n)^{3/2}`: `√ρ/log N = (log N)^{-1/4}` | `≤ τ/12` iff `log N ≥ (12/τ)^4` (τ=0.1: 2.07e8) | closure `∀τ ∀ᶠ n` |
| 13 | hidden copies for G2 | `AuxGraph2.lean` private helpers reached from `lwXiClaim_holds`: 17 decls, 244 lines (`priv2.py`); `lwN_zdistInf_le` private (`LWTermExpN.lean:403`); `auxGraph2_ev_poly` needs `ρ+1 ≤ N^τ`, not the polylog radius | `AuxGraph2.lean` is not writable: all copied into `LWXiExp.lean` | not in the ticket's size basis |
| 14 | §29 `EKTTkInf` / `AnpNearInfAt` | (1) `t<1`, `g²≤L²(1-t)` ⇒ `1-t>0`; (2) boundary `g²=L²(1-t)` included, as merged; (3) no `L,W` relation used; (4) `∃C` before `L,W,ℓ,Λ`, `n ≥ 2` | | |
| 15 | §29 `LWXiExpClaim` | (1) `0≤t≤lemT<1` ok; **(2) FAIL: conj 2 is claimed at `1-t < λ²/L²`** (row 8); (3) only `W ≥ N^𝔠` (Bandwidth) used; (4) `√ρ` hypothesis and every `Prec` are `∀ᶠ n`, `ℓ` is `∀ n` as `LWAssmExp` | | |
| 16 | §29 `lwTail32`, (A) | tail: (3) `W ≥ N^𝔠` is a stated `∀ᶠ`; (A): (1) `0≤t≤lemT`; (2) strict `λ²/L² < 1-t` in the subtype, as the target; (3) `W^{-1/𝔠} ≤ L^{-d}` from Bandwidth (`lwN_Wneg_le`); (4) `K` before `p`, `∀ᶠ n` | | |

### (ii) One concrete nondegenerate instance
`cd $S; python3 kw2.py; python3 sz.py | grep total; python3 priv2.py | tail -1`
```
referenced-private decls (outside copied segs), count 10 : lwMomExp_chain_nonneg:152 lwMomExp_step_aux:310 lwMomExp_sys_bound:434 lwMomExp_walk_chain:752 lwMomExp_path_ne:835 lwMomExp_sysOf_length:846 lwMomExp_sysOf_mem:851 lwMomExp_pathEdges:862 lwMomExp_pathEdges_card:874 lwMomExp_prod_split:882
private names in the STATEMENT of a needed decl: {'lwMomExp_walk_chain': ['lwMomExp_stepFn'], 'lwMomExp_pathEdges_card': ['lwMomExp_pathEdges'], 'lwMomExp_prod_split': ['lwMomExp_pathEdges']}
total kernel 309
private helpers of AuxGraph2 reached from lwXiClaim_holds (excluding auxGraph2_phi_cmp): 17 decls 244 lines; main theorem lines 141
```
`cd $S; python3 pre.py` (selected lines, verbatim; full output `pre.out`):
```
== B. EKTTkInf at d=3,n=2 (L=5,W=25,g=1/2,t=9/10,l=5,Lam=4)
 hyps: 0<W True  0<=g True  t<1 True  g^2<=L^2(1-t): 0.25 <= 2.4999999999999996  1<=l: True  l<=Lam*ellT: 5.0 <= 6.32455532033676 = 4.0 * 1.5811
 |D|= 125 of 125  (every alpha in D has |c-alpha|_inf<=l)
 max_{300 (x,y)} LHS/(Lam^2 W^-d/(1-t) Psi^0 prod sfT) =0.3784 ; proved constant 3*keyC_inf=6.502e+08 ; PASS=True
 ball-sum step (zdistD<=d*zdistInf; termwise comparison) on all 125 x: True
 violations: sfT_shift 0, tailT_shift 0, Phi_E hcmp 0
== B2. AnpNearInfAt hypotheses at the merged figAux data (L=6,W=2,g=1/2,t=1/2,l=Lam=2,c=a=0,b=e0, D=ball of radius l)
   g^2=0.25 <= L^2(1-t)=18.0 ; 1<=l ; ellT=1.000, l=2 <= Lam*ellT=2.000 ; |a-0|_inf=0<=2, |b-0|_inf=1<=2
 regime-1 (1-t>=g^2/L^2, s<=L): max R/(1+2^(d-1)) = 0.4338 (<=1, zeroMode_le_of_ge)
 sz0 n=500: L=2004 log10 N=54.9 t=lemT(z), 1-t=1.200e-44, lam^2/L^2=2.431e-43 -> regime 1-t<=g^2/L^2; R(s=L/2)=11.1
 sz0 n=500, z=i N^{-1+0.05}, t=lemT: 1-t=6.718e-53, g^2/L^2=2.431e-43, R(s=L/2)=1.81e+09 = N^0.169 ; allowed N^(2tau)=310364 for tau=0.05
 sz0 n=500, z=i N^{-1+0.02}, t=lemT: 1-t=1.512e-54, g^2/L^2=2.431e-43, R(s=L/2)=8.05e+10 = N^0.199 ; allowed N^(2tau)=310364 for tau=0.05
 violations 0 / 60000, max Phi^2/bound=0.2323
   p=2 K=6 tau'=0.05 d=3: log W >= 7.111e+04
   a=3 b=2 c=1 cfrak=1/6: M=60, log W>=3600 ; exponent at threshold: -c x^{3/2}/2 + a y = -43200 <= -b y = -43200 : True
   tau=0.1: tau'=0.008333 -> log N >= 2.074e+08 (Kn<=N^{tau/8}, 2(2rho+1)^{2d}<=N^{tau/4} follow, rho polylog)
 n=500: t=1/2<=lemT=1.000000; lam^2/L^2=2.43e-43<1-t ; WO: W^(-d/2+dd)=9.86e-22<=lam=9.88e-19<=10 ; W>=N^(1/6): True ; ellT=1 ; K(logW)^(3/2)ellT=1218.4 vs max|a-b|_inf=L/2=1002 ; log W=34.5
```
Instance for `ekTTkInf` (d=3, n=2, L=ℓ=5, W=25, g=1/2, t=9/10, Λ=4, D = all 125 points) and `AnpNearInfAt 3 figAux` (L=6, W=2, g=1/2, t=1/2, ℓ=Λ=2): every hypothesis holds (lines B, B2). Stochastic targets (`lwXiExpClaim`, `lwMomExpNoExp` at p=2, K=6): merged `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `λ=(2(n+1))^{-6}`, `κ=ε=𝔡=1/10`, `𝔠=1/6`), n=500, `t=1/2 ≤ lemT(z)` (regime-1, subtype nonempty), `ℓ_t=1`, `K(log W)^{3/2}ℓ_t = 1218 ≥ L/2 = 1002` (every pair in `regA`); WO and `W ≥ N^{1/6}` hold (last line). `LWLoopExp`, `LWInit` are other gates' pins and stay hypotheses. External hypothesis `∀τ>0 ∀ᶠ n √ρ_n ≤ τ log N_n`, `ρ_n=(log N_n)^{3/2}`: limit `√ρ_n/log N_n = (log N_n)^{-1/4} → 0` as `N_n=(W_nL_n)^3 → ∞`; threshold `log N ≥ (12/τ)^4`. The conclusions of `≺`-statements are eventual (`∀τ ∀ᶠ n`), thresholds in rows 9, 11, 12.

### Verdict per target (stage 1a)
- `ekTTkInf_holds`: PASS (rows 3-5, script B). Ticket list of kernel lemmas must add `sfT_TtTt`, `sfT_KtKt`, `sfT_pair_cases` (row 3).
- `lwMomExp_nearInf`: PASS (rows 1-2, 5; 11 keywords exact).
- `lwTail32`: PASS (row 11; proved in the probe `:467`).
- `lwMomExpNoExp_holds`: PASS for every `K>0` (rows 9-10, script F).
- `lwXiExpClaim_holds`: **FAIL** (mathematical; row 8, 15). The pinned conclusion has conjunct 2 `ξ ≺ 𝖳(|·|∞∧ℓ)+W^{-D}` for all `n`, but `LWLoopExp` only gives loops `≲ W^{-d} tailW` whose zero mode `(L^d(1-t))⁻¹` is not `≲ 𝖳²` when `1-t < λ²/L²` (merged `LWPsi.lean:437-439` says the same; sz0 at `t=lemT(z)` is in that regime for n=0,5,500, E). Loop values permitted by the hypothesis give `ξ(a₁,a₂)² ≥ W^{-d}tailT` at `(a₁,a₂)`, so no proof exists from the hypotheses. Required correction: conjunct 2 over `{p // lam n²/L n² < 1 - t n}` (as `LWMomentExp`), class `Φ_E = (W^{-d}tailW)^{1/2}`; with it rows 6-8, 12 close and conjuncts 1, 3 are unchanged.
- Not a size verdict: rows 3, 13 add 85 + 244 measured source lines absent from the ticket's list (for the dispatcher's C2 test).
