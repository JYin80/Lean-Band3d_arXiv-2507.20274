Prover model: claude-sonnet-5-5
## (a) Math preflight — Fri Oct  9 03:07:04 UTC 2026
Restart under CONTROL H149 / Amend 1 (re-released check file, conjunct 2 of `LWXiE` on the subtype `λ²/L² < 1-t`). Scripts (python, no Lean) in `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2359`: `kw2.py`, `sz.py`, `priv2.py`, `pre.py` (rows 3-5, 9-12 re-run: output identical to the one of `docs/reports/T2359-prove-1a0.md`), `pre2.py` (new, rows 6-8, 12). Worktree `t/T2359` at `1fcb883`.
Notation: `𝖳 = sfT`, `m = min(r,ℓ)`, `r = |a₁-a₂|_∞`, `D' = 2D`, `Φ_E(r) := (W^{-d} tailW_{ℓ,W,D'}(r))^{1/2}`, `Φ_E² = W^{-d} max(tailT(m), W^{-D'})`, `k = d-2`.

### (i) Exponent table
| # | item | value | constraint | slack |
|---|---|---|---|---|
| 1 | de-privatised keywords `LWMomExp.lean` | 11: chain_nonneg 152, step_aux 310, sys_bound 434, stepFn 710, walk_chain 752, path_ne 835, sysOf_length 846, sysOf_mem 851, pathEdges 862, pathEdges_card 874, prod_split 882 (each line is `private`, checked) | 10 referenced by the copied segments (`kw2.py`); `stepFn` occurs in the statement of `walk_chain`; `pathEdges` in those of `pathEdges_card`, `prod_split` | 0 spare; `_disj`, `path_split`, `walk_last/visit`, `stepFn_eq`, `base`, `marks` stay private |
| 2 | segments copied from `LWMomExp.lean` | tau block 521-581; `TTkBody`…`sys_near` 584-699; `nSolid`, `ordN`, `near_graph`, `near` 918-1024 (268 lines, `sz.py`) | `zdistD ↦ zdistInf` in `tau` (521-525), `TTkBody` (`hD`, `x y`), `hstep` (centre `c`, `D` with `∀α∈D, |c-α|∞ ≤ ℓ` replaces `nearD`), last line of `near_graph`; symmetry `anpKey_zdistInf_neg` (`AnpKey.lean:91`) | generic part 304-516 has no `zdist`: not copied |
| 3 | kernel copies (`PropT.lean`) | ticket: `sfT_pair_le` 788, `prod_sfT_pair_le` 839, `key_T_reduce` 913, `key_T_reduce_absorbed` 1056; **plus `sfT_TtTt` 644, `sfT_KtKt` 672, `sfT_pair_cases` 690** (`sfT_pair_le:811` calls `sfT_pair_cases`; `sfT_TtTt:659` uses `zdistD_add_le`); Amend 1 lists them | triangle `anpKey_zdistInf_tri` (`AnpKey.lean:101`) and symmetry only | 7 decls, 309 source lines (`sz.py`) |
| 4 | `C_∞ = 3·keyC∞(k,n)`, `keyC∞ = (√2^k)^n·4·d^{k+2}·ballC k` | d=3, n=2: 6.50e8 | `D ⊂ ℓ^∞`-ball(c,ℓ) ⊂ `ℓ¹`-ball(c,dℓ) (`zdistD_le_mul_zdistInf`, `Defs/Sizes.lean:122`); `min(r₁,dℓ)+1 ≤ d(min(r_∞,ℓ)+1)`; `1 ≤ dℓ` | `C` depends on `d,n` only; needed C at the instance 0.378 |
| 5 | hypotheses of `EKTTkInf`, `AnpNearInfAt` | `t<1`, `0≤g`, `g² ≤ L²(1-t)`, `1 ≤ ℓ ≤ Λℓ_t` | as merged `EKTTk` (non-strict) | figAux data meets `ℓ ≤ Λℓ_t` with equality (ℓ_t = 1) |
| 6 | class for G2 | `Φ_E` above, `D' = 2D`. (c1) `Φ_E>0` for `W>0`: `tailW_pos` (`Defs/Tail.lean:105`). (c2) `LWLoop2 Φ_E` is `LWLoopExp` (`LWPins.lean:274`) at `D'` verbatim (`Φ_E² = W^{-d}tailW` by `Real.sq_sqrt`, same `zdistInf` argument, same `ℓ` from `LWAssmExp`). (c3) window `W^{-d/2} ≤ C₃Φ_E(0)`, `C₃² = 1+𝔡⁻²`: `tailW(0) ≥ tailT(0) = Bparam 0 ≥ (λ²+1-t)⁻¹`, `λ ≤ 𝔡⁻¹` (`WO`, `Defs/Sizes.lean:164`), `0 ≤ t < 1` | regime-free (`Bparam` keeps the zero mode) | script C: 0/200000 violations |
| 7 | `hcmp` for `Φ_E` | `Φ_E(m)² ≤ Kn²Φ_E(ℓ')²` for `0≤ℓ' ≤ 2ρ+m`, `Kn² = (2ρ+1)^{d-2} e^{√(2ρ/ℓ_t)}`: `min(ℓ',ℓ) ≤ 2ρ+min(m,ℓ)`; B-part `s'+1 ≤ (2ρ+1)(s+1)`, zero mode common to numerator and denominator; exp-part `sqrt_le_add_sqrt_shift`; floor `W^{-D'}` via `Kn ≥ 1`, `ℓ_t ≥ 1` (`one_le_ellT`) | `Kn ≤ N^{τ/8}`: `N^{τ/16}` each; `½√(2ρ) ≤ (τ/16) log N` iff `√ρ ≤ 0.0884 τ log N`; hypothesis used at `τ' = τ/12` | slack 5.7% (script E); script D: 0/300000 violations, max ratio 0.9937 |
| 8 | **comparison to the target on the subtype** (c5): `Φ_E(r)² ≤ (1+2^{d-1})𝖳(m)² + W^{-d-D'}`, then `Φ_E(r) ≤ √(1+2^{d-1})(𝖳(m)+W^{-D})` (`W ≥ 1`, `W^{-(d+2D)/2} ≤ W^{-D}`) | `W^{-d}tailT(m) = W^{-d}e^{-√(m/ℓ_t)}(A(m+1)^{-k}+Z)`, `A=(g²+|1-t|)⁻¹`, `Z=(L^d|1-t|)⁻¹`; `zeroMode_le_of_ge` (`Defs/Tail.lean:119`: `hd: 2 ≤ d`, `1 ≤ L`, `t<1`, `0 ≤ m ≤ L`, `g²/L² ≤ 1-t`) gives `Z ≤ 2^{d-1}A(m+1)^{-k}` | on the subtype `λ²/L² < 1-t` gives `g²/L² ≤ 1-t`; `m ≤ r ≤ L` by `zdistInf ≤ L` (`lwN_zdistInf_le`, `LWTermExpN.lean:403`, private: copied); then `N^{τ/2}·√(1+2^{d-1}) ≤ N^τ` eventually | max `(R-1)/2^{d-1}` = 0.3704 (script A, 4e5 draws incl. `1-t ↓ g²/L²`); 0 violations. Link false off the subtype: `docs/reports/T2359-prove-1a0.md` row 8, script E (`N^{0.17..0.20}`) |
| 9 | (A) chain at general `K>0` | `Φ_B(cr)² ≤ (1+2^{d-1})(2/min(c,1))^{d-2} e^{√(m/ℓ_t)} 𝖳(m)²`; `regA ⇒ m/ℓ_t ≤ K(log W)^{3/2}`; loss `e^{(p/2)√K (log W)^{3/4}}` | `≤ N^{τ'}` iff `log W ≥ (p√K/(2τ'd))^4` (`log N ≥ d log W`); p=2,K=6,τ'=.05,d=3: 7.1e4 | factor `e^{-√K(log W)^{3/4}}` is `N^{-o(1)}`, `K` enters the threshold only; script F 0/60000 violations, max ratio 0.23 |
| 10 | (A) constants and quantifiers | `LWPhiB_psiAll` (`LWPsi.lean:422`): `(C₁,C₂,C₃,Cc) = (2^d, d, √(1+Λ²), C↦√((C+1)^{d-2}))`, depends on `d,Λ=𝔡⁻¹` only (before `ε₀`, `c` in `LWMoment`); `ε₁ = min(ε₀, d c₁/2)`, `c₁ = min(2𝔡𝔠,ε)/2` instantiated inside, after `𝔠`; `c` from `∃c` of `lwMoment_holds` | `c ≥ 1`: antitone; `c<1`: factor `2/c` | `LWLoop2` for `Φ_B` from `lwN_tailW_le` (`LWTermExpN.lean:121`, all regimes) |
| 11 | `lwTail32` | `log W ≥ (2A/(𝔠c))²`, `A = |a|+|b|` | worst case `log N = log W/𝔠` | equality at threshold (script G); `c>0` free (C4 (c)) |
| 12 | G2 radius | `ρ_n = (log N_n)^{3/2}`: `√ρ/log N = (log N)^{-1/4}`; `(2ρ+1)^{(d-2)/2}`, `2(2ρ+1)^{2d}`, `ρ+1` are polylog, `≤ N^σ` eventually (`SizeTendsto`) | `√ρ ≤ (τ/12) log N` iff `log N ≥ (12/τ)^4` (τ=0.1: 2.07e8) | closure `∀τ ∀ᶠ n`; script E |
| 13 | hidden copies for G2 | 17 private `AuxGraph2` decls reached from `lwXiClaim_holds` (244 lines, `priv2.py`), main theorem 141 lines; `auxGraph2_phi_cmp` is replaced by row 7; `auxGraph2_ev_poly` needs `ρ+1 ≤ N^τ`: derived from row 12 | `AuxGraph2.lean` not writable: copied into `LWXiExp.lean` | Amend 1 includes them |
| 14 | §29 `EKTTkInf` / `AnpNearInfAt` | (1) `t<1`, `g²≤L²(1-t)` ⇒ `1-t>0`; (2) boundary `g²=L²(1-t)` included, as merged; (3) no `L,W` relation used; (4) `∃C` before `L,W,ℓ,Λ`, `n ≥ 2` | | |
| 15 | §29 `LWXiExpClaim` (new pin) | (1) `0≤t≤lemT<1`; (2) conjunct 2 only where `λ²/L² < 1-t` (strict, as `LWMomentExp`); conjuncts 1, 3 unchanged (conj 3 = Ward, no class); (3) `WO` and `W ≥ N^𝔠` from `STFlow`; (4) the `√ρ` hypothesis and every `Prec` are `∀ᶠ n`; `ℓ` is `∀ n` as `LWAssmExp`; the failure event on the subtype is mapped to the loop failure event with any `s : Bool` (`auxGraph2_prec_of_imp`, `U ≠ V` allowed) | | |
| 16 | §29 `lwTail32`, (A) | tail: `W ≥ N^𝔠` is a stated `∀ᶠ`; (A): (1) `0≤t≤lemT`; (2) strict `λ²/L² < 1-t` in the subtype, as the target; (3) `W^{-1/𝔠} ≤ L^{-d}` from Bandwidth (`lwN_Wneg_le`); (4) `K` before `p`, `∀ᶠ n` | | |

### (ii) One concrete nondegenerate instance
`cd $S; python3 kw2.py; python3 sz.py | tail -1; python3 priv2.py | tail -1`
```
referenced-private decls (outside copied segs), count 10 : lwMomExp_chain_nonneg:152 lwMomExp_step_aux:310 lwMomExp_sys_bound:434 lwMomExp_walk_chain:752 lwMomExp_path_ne:835 lwMomExp_sysOf_length:846 lwMomExp_sysOf_mem:851 lwMomExp_pathEdges:862 lwMomExp_pathEdges_card:874 lwMomExp_prod_split:882
private names in the STATEMENT of a needed decl: {'lwMomExp_walk_chain': ['lwMomExp_stepFn'], 'lwMomExp_pathEdges_card': ['lwMomExp_pathEdges'], 'lwMomExp_prod_split': ['lwMomExp_pathEdges']}
total LWMomExp copy 268
private helpers of AuxGraph2 reached from lwXiClaim_holds (excluding auxGraph2_phi_cmp): 17 decls 244 lines; main theorem lines 141
```
`cd $S; python3 pre2.py` (verbatim):
```
== A. conjunct 2 on the subtype lam^2/L^2 < 1-t: Phi_E(r)^2 <= (1+2^(d-1)) sfT(m)^2 + W^(-d-D'),  m=min(r,l), 0<=r<=L, D'=2D
 violations: squared form 0, sqrt form 0 (of ~400000 draws); max lhs/rhs=1.0000 ; max (R-1)/2^(d-1)=0.3704 (<=1 is zeroMode_le_of_ge)
== C. window: W^-d <= C3^2 Phi_E(0)^2 with C3^2=1+dd^-2, lam<=dd^-1 (WO), 0<=t<1
 violations 0 / 200000
== D. hcmp for Phi_E (all regimes): Phi_E(m)^2 <= Kn^2 Phi_E(l')^2 for 0<=l'<=2rho+m, Kn^2=(2rho+1)^(d-2) exp(sqrt(2rho/ell_t))
 violations 0 / 300000, max ratio 0.9937
== E. exponent closure: Kn<=N^(tau/8) from sqrt(rho)<=tau' log N, tau'=tau/12 (need tau'<=tau/(8 sqrt2)):
 tau/(8*sqrt2) = 0.088388 tau ; tau/12 = 0.083333 tau ; slack 5.7%
 tau=0.2: at log N=1.0e+10 rho=(log N)^1.5: sqrt(rho)/log N=3.162e-03<=tau/12=1.667e-02 ; log Kn=2.236e+07 <= (tau/8) log N=2.5e+08 : True
 tau=0.1: at log N=1.0e+10 rho=(log N)^1.5: sqrt(rho)/log N=3.162e-03<=tau/12=8.333e-03 ; log Kn=2.236e+07 <= (tau/8) log N=1.25e+08 : True
```
`cd $S; python3 pre.py` (lines 1-5, 8-9, 11, 14, 31-33 of the output, verbatim):
```
== B. EKTTkInf at d=3,n=2 (L=5,W=25,g=1/2,t=9/10,l=5,Lam=4)
 hyps: 0<W True  0<=g True  t<1 True  g^2<=L^2(1-t): 0.25 <= 2.4999999999999996  1<=l: True  l<=Lam*ellT: 5.0 <= 6.32455532033676 = 4.0 * 1.5811
 |D|= 125 of 125  (every alpha in D has |c-alpha|_inf<=l)
 max_{300 (x,y)} LHS/(Lam^2 W^-d/(1-t) Psi^0 prod sfT) =0.3784 ; proved constant 3*keyC_inf=6.502e+08 ; PASS=True
 ball-sum step (zdistD<=d*zdistInf; termwise comparison) on all 125 x: True
== B2. AnpNearInfAt hypotheses at the merged figAux data (L=6,W=2,g=1/2,t=1/2,l=Lam=2,c=a=0,b=e0, D=ball of radius l)
   g^2=0.25 <= L^2(1-t)=18.0 ; 1<=l ; ellT=1.000, l=2 <= Lam*ellT=2.000 ; |a-0|_inf=0<=2, |b-0|_inf=1<=2
 regime-1 (1-t>=g^2/L^2, s<=L): max R/(1+2^(d-1)) = 0.4338 (<=1, zeroMode_le_of_ge)
 sz0 n=500: L=2004 log10 N=54.9 t=lemT(z), 1-t=1.200e-44, lam^2/L^2=2.431e-43 -> regime 1-t<=g^2/L^2; R(s=L/2)=11.1
 n=0: t=1/2<=lemT=0.999991; lam^2/L^2=1.53e-05<1-t ; WO: W^(-d/2+dd)=7.81e-03<=lam=1.56e-02<=10 ; W>=N^(1/6): True ; ellT=1 ; K(logW)^(3/2)ellT=38.7 vs max|a-b|_inf=L/2=2 ; log W=3.5
 n=5: t=1/2<=lemT=1.000000; lam^2/L^2=1.95e-16<1-t ; WO: W^(-d/2+dd)=2.79e-08<=lam=3.35e-07<=10 ; W>=N^(1/6): True ; ellT=1 ; K(logW)^(3/2)ellT=262.8 vs max|a-b|_inf=L/2=12 ; log W=12.4
 n=500: t=1/2<=lemT=1.000000; lam^2/L^2=2.43e-43<1-t ; WO: W^(-d/2+dd)=9.86e-22<=lam=9.88e-19<=10 ; W>=N^(1/6): True ; ellT=1 ; K(logW)^(3/2)ellT=1218.4 vs max|a-b|_inf=L/2=1002 ; log W=34.5
```
Instances: `ekTTkInf` at d=3, n=2, L=ℓ=5, W=25, g=1/2, t=9/10, Λ=4, D = all 125 points; `AnpNearInfAt 3 figAux` at L=6, W=2, g=1/2, t=1/2, ℓ=Λ=2 (all hypotheses hold: `pre.py` lines 1-2, 8-9). Stochastic targets (`lwXiExpClaim`, `lwMomExpNoExp` at p=2, K=6): merged `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `λ=(2(n+1))^{-6}`, `κ=ε=𝔡=1/10`, `𝔠=1/6`), n=500, `t=1/2 ≤ lemT(z)`: `λ²/L² = 2.43e-43 < 1-t`, so the subtype of conjunct 2 and the subtype of (A) are nonempty; `ℓ_t=1`, `K(log W)^{3/2}ℓ_t = 1218 ≥ L/2 = 1002` (every pair in `regA`); WO and `W ≥ N^{1/6}` hold (`pre.py` line 33). At `t = lemT(z)` the subtype is empty for n=0,5,500 (`pre.out` lines 12-14), so the pin is vacuous there and the instance uses `t=1/2`. `LWLoopExp`, `LWInit`, `‖G-M‖ ≺ W^{-ε₁}` are other gates' pins and stay hypotheses. External hypothesis `∀τ>0 ∀ᶠ n √ρ_n ≤ τ log N_n`, `ρ_n=(log N_n)^{3/2}`: limit `√ρ_n/log N_n = (log N_n)^{-1/4} → 0` as `N_n=(W_nL_n)^3 → ∞`; threshold `log N ≥ (12/τ)^4` (script E, `pre.out` section H).

### Verdict per target (stage 1a)
- `ekTTkInf_holds`: PASS (rows 3-5, `pre.py` line 4).
- `lwMomExp_nearInf`: PASS (rows 1-2, 5; 11 keywords exact).
- `lwTail32`: PASS (row 11; proved in the probe `:467`).
- `lwMomExpNoExp_holds`: PASS for every `K>0` (rows 9-10, script F).
- `lwXiExpClaim_holds` (Amend 1 pin, conjunct 2 on `λ²/L² < 1-t`): PASS. Links: (c1)-(c3) rows 6; `hcmp` row 7; comparison to the target row 8 (the link that failed in `T2359-prove-1a0.md` holds on the subtype with constant `1+2^{d-1}`, script A); exponent closure rows 7, 12; conjuncts 1, 3 unchanged. Kernel copy list = ticket + `sfT_TtTt`, `sfT_KtKt`, `sfT_pair_cases` (row 3); private copies row 13.
## (b) Script output — Fri Oct  9 03:52:50 UTC 2026
Branch `t/T2359` (base `1fcb883`), tip `ed12748`, `git status --short`: `clean`.  Scratch (outside the repo, `S` = the scratchpad `T2359/` directory): `S/{stmts,insts,clash,names,mkreport}.py` (python3), `S/lean/{checkeq,registry,chk}.lean` (Lean, not committed).
### b.1 Commits and the stop rule (`wc -l` of the three new files at each commit, UTC time of the commit; stop line 2100)
```
$ for C in `git log --reverse --format=%h main..t/T2359`: git show C:RBM3D/Graph/{LWMomExpInf,LWXiExp,LWMomentExpA}.lean | wc -l
23c252d 03:12:33Z M   0 X   0 A   0 sum    0  T2359: LWMomExp.lean, remove private from the 11 keywords 
673797b 03:18:23Z M 610 X   0 A   0 sum  610  T2359: LWMomExpInf.lean (M): claim:TTk and the near pin in
8f16ef6 03:30:15Z M 610 X 787 A   0 sum 1397  T2359: LWXiExp.lean (X): claim:xi for the exp class, lwTai
7882e64 03:41:54Z M 610 X 787 A 460 sum 1857  T2359: LWMomentExpA.lean (A): lem:LW_moment_exp in the no-
ed12748 03:46:52Z M 615 X 787 A 460 sum 1862  T2359: private near_graph helper, instance namespace LWMom
```
### b.2 Builds, registry pre-check, check-file equality, axioms (tip)
```
$ lake build RBM3D.Graph.LWMomExpInf RBM3D.Graph.LWXiExp RBM3D.Graph.LWMomentExpA 2>&1 | tail -1
Build completed successfully (3899 jobs).
$ lake build 2>&1 | tail -1    # whole library incl. `#assert_rbm_axioms` of RBM3D.lean (the root imports the new modules at merge, hub step 4)
Build completed successfully (4170 jobs).
$ lake env lean S/lean/registry.lean   # uncommitted: `import RBM3D` + the three new imports + `#assert_rbm_axioms`
exit 0; 259 output lines; first: axiom audit: 10542 theorems, 3090 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean S/lean/checkeq.lean   # the re-released check file + the three new imports + the five examples below; checkeq exit: 0; lines containing `error`: 0
example : RBM.Graph.T2359Check.T2359_ekTTkInf_holds := RBM.Graph.ekTTkInf_holds
example : RBM.Graph.T2359Check.T2359_lwMomExp_nearInf := RBM.Graph.lwMomExp_nearInf
example : RBM.Graph.T2359Check.T2359_lwXiExpClaim_holds := RBM.Graph.lwXiExpClaim_holds
example : RBM.Graph.T2359Check.T2359_lwMomExpNoExp_holds := RBM.Graph.lwMomExpNoExp_holds
example : RBM.Graph.T2359Check.T2359_lwTail32 := @RBM.Graph.lwTail32
'RBM.Graph.ekTTkInf_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_nearInf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiExpClaim_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpNoExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwTail32' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### b.3 `LWMomExp.lean` keyword diff, diff stat, forbidden tokens
```
$ git diff main...t/T2359 -- RBM3D/Graph/LWMomExp.lean | script: pair each - line with its + line
deleted 11, added 11, every pair differs only by the prefix `private `: True
names: lwMomExp_chain_nonneg lwMomExp_step_aux lwMomExp_sys_bound lwMomExp_stepFn lwMomExp_walk_chain lwMomExp_path_ne lwMomExp_sysOf_length lwMomExp_sysOf_mem lwMomExp_pathEdges lwMomExp_pathEdges_card lwMomExp_prod_split
$ git diff --stat main...t/T2359
 RBM3D/Graph/LWMomExp.lean     |  22 +-
 RBM3D/Graph/LWMomExpInf.lean  | 615 +++++++++++++++++++++++++++++++++
 RBM3D/Graph/LWMomentExpA.lean | 460 ++++++++++++++++++++++++
 RBM3D/Graph/LWXiExp.lean      | 787 ++++++++++++++++++++++++++++++++++++++++++
 4 files changed, 1873 insertions(+), 11 deletions(-)
$ grep -n 'sorry\|admit\|native_decide\|^ *axiom ' <the three files> | wc -l
0
```
### b.4 Target statements, extracted from the files by `stmts.py` (`identical-to-check` is a textual comparison with the check file, prefix `T2359_` removed)
```
== Prop definitions (file:lines), and diff against the check file section 2 (prefix T2359_ removed)
-- LWMomExpInf.lean:48-55  check:50-57  identical-to-check: True
def EKTTkInf (d n : ℕ) : Prop :=
  3 ≤ d → 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
      ∀ (D : Finset (Zd d L)) (c : Zd d L), (∀ α ∈ D, (zdistInf d L (c - α) : ℝ) ≤ ℓ) → ∀ x y : Fin n → Zd d L,
        ∑ α ∈ D, ∏ i, (sfT d L W g t (min (zdistInf d L (x i - α) : ℝ) ℓ) * sfT d L W g t (min (zdistInf d L (y i - α) : ℝ) ℓ))
          ≤ C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
              (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ))
-- LWMomExpInf.lean:59-67  check:59-67  identical-to-check: True
def AnpNearInfAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
        ∀ (c a b : Zd d L) (D : Finset (Zd d L)), (∀ α ∈ D, ((zdistInf d L (c - α) : ℕ) : ℝ) ≤ ℓ) →
          lwMomExp_valOnD Γ ξ (fun _ => a) (fun _ => b) D ≤
            C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
              sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p
-- LWMomExpInf.lean:70-71  check:93-94  identical-to-check: True
def AnpNearInf (d : ℕ) : Prop :=
  3 ≤ d → ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → AnpNearInfAt d Γ
-- LWXiExp.lean:57-64  check:69-76  identical-to-check: True
def LWXiE {d : ℕ} (sz : Sizes d) (E t ℓ : ℕ → ℝ) (D : ℝ) (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    sz.Prec (U := fun n => {_p : Zd d (sz.L n) × Zd d (sz.L n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n p ω => ξ n p.1.1 p.1.2 ω)
      (fun n p _ => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
    sz.Prec (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (E n) (t n))⁻¹)
-- LWXiExp.lean:68-75  check:78-85  identical-to-check: True
def LWXiExpClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
      ∀ ε₁ : ℝ, 0 < ε₁ → sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
        ∀ D : ℝ, 0 < D → ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
          (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ)) →
          LWXiE sz (STflowE z) t ℓ D (lwXiVar sz (STflowE z) t ρ)
-- LWMomentExpA.lean:49-52  check:87-90  identical-to-check: True
def regA (d : ℕ) (K : ℝ) (sz : Sizes d) (n : ℕ) (t ℓ : ℝ) (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : Prop :=
  ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ) ≤
      K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) t ∨
    ℓ ≤ K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) t
-- LWMomentExpA.lean:56-65  check:98-107  identical-to-check: True
def LWMomExpNoExpF (d : ℕ) (K : ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D →
        sz.Prec (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ regA d K sz n (t n) (ℓ n) q})
          (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ∂(sz.seqP))
          (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
            sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D))
== target theorems
-- LWMomExpInf.lean:282-282
theorem ekTTkInf_holds (d n : ℕ) : EKTTkInf d n := by
-- LWMomExpInf.lean:547-547
theorem lwMomExp_nearInf : ∀ d, AnpNearInf d :=
-- LWXiExp.lean:568-568
theorem lwXiExpClaim_holds (d : ℕ) : LWXiExpClaim d := by
-- LWMomentExpA.lean:334-334
theorem lwMomExpNoExp_holds : ∀ (d : ℕ) (K : ℝ), 0 < K → LWMomExpNoExpF d K := by
-- LWXiExp.lean:81-84
theorem lwTail32 {d : ℕ} (sz : Sizes d) {𝔠 c : ℝ} (h𝔠 : 0 < 𝔠) (hc : 0 < c) (hsz : sz.SizeTendsto)
    (hband : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) (a b : ℝ) :
    ∀ᶠ n in atTop, Real.exp (-(c * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) / 2)) * ((sz.size n : ℕ) : ℝ) ^ a ≤
      ((sz.size n : ℕ) : ℝ) ^ (-b) := by
```
### b.5 Compiled nonempty instances (`insts.py`: `file:line: statement head || application`)
```
LWMomExpInf.lean:569: example : ∑ α : Zd (1 + 2) 5, ((min ((zdistInf (1 + 2) 5 (0 - α) : ℕ) : ℝ) 5 + 1) ^ 1)⁻¹ ≤ || sum_ball_inf_min_pow_le 1 (by norm_num) Finset.univ 0 0 fun α _ => by
LWMomExpInf.lean:575: theorem inst_ekTTkInf : ∃ C : ℝ, 0 < C ∧ || by ...
LWMomExpInf.lean:589: theorem inst_near : AnpNearInfAt 3 figAux := || lwMomExp_nearInf 3 le_rfl 2 2 figAux figAux_nested.2 figAux_nested.1
LWMomExpInf.lean:593: theorem inst_near_pt : ∃ C : ℝ, 0 < C ∧ || by ...
LWXiExp.lean:760: example : ∀ n, Nonempty {_p : Zd 3 (sz0.L n) × Zd 3 (sz0.L n) // sz0.lam n ^ 2 / ((sz0.L n : ℕ)  || fun n => ⟨⟨(0, 0), strict_all n⟩⟩
LWXiExp.lean:766: example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst  || lwXiExpClaim_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_
LWXiExp.lean:774: example : ∀ᶠ n in atTop, Real.exp (-(1 * Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) / 2)) * || lwTail32 sz0 (by norm_num) one_pos sz0_admissible.2.2.1 sz0_admissible.2.2.2.1
LWXiExp.lean:779: example : ∀ᶠ n in atTop, Real.exp (-(1 / 4 * Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) / 2)) * || lwTail32 sz0 (by norm_num) (by norm_num) sz0_admissible.2.2.1 sz0_admissible.2
LWMomentExpA.lean:418: example (K : ℝ) (hK : 0 < K) (n : ℕ) : || by ...
LWMomentExpA.lean:429: example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst  || lwMomExpNoExp_holds 3 6 (by norm_num) le_rfl (1 / 10) (1 / 10) (1 / 10) (by no
LWMomentExpA.lean:443: example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst  || lwMomExpNoExp_holds 3 (1 / 2) (by norm_num) le_rfl (1 / 10) (1 / 10) (1 / 10) 
```
### b.6 Name-clash grep of the new public names (`clash.py`) and ports
```
public declarations of the three files: 19; plus 2 names of the ticket list not introduced: ['sfT_shift_le', 'sqrt_le_add_sqrt_shift']
grep -rwn --include=*.lean NAME RBM3D | grep -v <the three files> | grep -v /Probe/  -> hits per name:
EKTTkInf=0 AnpNearInfAt=0 AnpNearInf=0 sum_ball_inf_min_pow_le=0 lwMEI_keyC=0 ekTTkInf_holds=0 lwMEI_tau=0 
lwMomExp_nearInf=0 inst_ekTTkInf=0 inst_near=0 inst_near_pt=0 LWXiE=0 LWXiExpClaim=0 lwTail32=0 lwXE_phi=0 
lwXiExpClaim_holds=0 regA=0 LWMomExpNoExpF=0 lwMomExpNoExp_holds=0 sfT_shift_le=0 sqrt_le_add_sqrt_shift=0 
total hits: 0
```
Ports: none from RBM1D/RBM2D (read-only, no light-weight graph layer, not opened).  Copies: (1) merged RBM3D files (`git log -1 --format=%h 1fcb883 -- <the five sources>` = `1546ef7`); (2) the never-merged probe `t/T2348:RBM3D/Probe/T2348Pins.lean` (`git log -1 --format=%h t/T2348 -- <it>` = `9f3bd75`) for `sum_ball_inf_min_pow_le` (line 358) and `lwTail32` (line 467); the line ranges are in the "Ports" paragraph of each file docstring.
### b.7 Route evidence
```
$ grep -n 'sfT_mul_le_TtTt\|sfT_mul_le_KtKt\|anpKey_zdistInf_tri\|lwMomExp_sys_bound' RBM3D/Graph/LWMomExpInf.lean | cut -c1-100   # the comment lines 24, 304 mention step_aux/sys_bound
24:  (the generic chain `lwMomExp_sys_bound` of `Graph/LWMomExp.lean:434` is reused), `lwMomExp_near
116:  have h := anpKey_zdistInf_tri x α y
141:      exact sfT_mul_le_TtTt hW hp hq (le_min hs hℓ) ((min_le_left _ _).trans hspq)
143:      exact (sfT_mul_le_KtKt hW hq).trans (hfin q)
145:    exact (sfT_mul_le_KtKt hW (le_min hp hℓ)).trans (hfin _)
304:The generic chain of `Graph/LWMomExp.lean` (`lwMomExp_step_aux`, `lwMomExp_sys_bound`: no `zdist
434:  exact lwMomExp_sys_bound (lwMEI_tau d L W g t ℓ) (sfT d L W g t 0) (PsiT d L W g t) K _ N D a 
$ grep -c '^private theorem lwXE_\|^private def lwXE_' RBM3D/Graph/LWXiExp.lean
27
```
### b.8 Narrative
- Result: the five targets are proved and committed on `t/T2359`: `ekTTkInf_holds`, `lwMomExp_nearInf` (`LWMomExpInf.lean`); `lwXiExpClaim_holds`, `lwTail32` (`LWXiExp.lean`); `lwMomExpNoExp_holds` for every `K > 0` (`LWMomentExpA.lean`). The seven Prop definitions are textually the check file's (b.4); the check-file equality, the three-module and full builds and the registry pre-check pass (b.2); the axioms are the three standard ones; `LWMomExp.lean` changes by exactly the 11 `private ` deletions (b.3). The stop line 2100 was not reached (largest sum 1862, b.1): no cut, no REQ.
- (M) The pair bound `lwMEI_pair_le` is one real-variable lemma (cases `q ≤ ℓ`; `p ≤ ℓ` or `ℓ ≤ p`; `ℓ ≤ q`) on the merged `sfT_mul_le_TtTt`/`sfT_mul_le_KtKt` with the triangle inequality `anpKey_zdistInf_tri` (b.7); so the four lattice-level kernel copies of (a) row 3 (`sfT_TtTt`, `sfT_KtKt`, `sfT_pair_cases`, `sfT_pair_le`) are not made. `lwMEI_key` is the `zdistInf` twin of `key_T_reduce` with the ball sum `sum_ball_inf_min_pow_le` (constant `4 d^{k+2} ballC_k`); `lwMEI_near_graph` uses the generic `lwMomExp_sys_bound` and the de-privatised helpers. `lwMomExp_step_aux` is public as C4 (a) lists, but no code of the three files calls it (b.7).
- (X) `Φ_E = lwXE_phi = (W^{-d} wT_{ℓ,W,2D})^{1/2}`; the loop bound is `hloopE (2*D)` (`LWLoopExp` at `2D`); `lwXE_phi_cmp` is `Φ_E(m) ≤ K_n Φ_E(ℓ')` for `ℓ' ≤ 2ρ+m`, `K_n = ((2ρ+1)^{d-2} e^{√(2ρ/ℓ_t)})^{1/2}`, in every regime (shift of `tailT`; the floor `W^{-D}` is absorbed since the factor is `≥ 1`); `lwXE_window`: `W^{-d} ≤ (1+𝔡⁻²) Φ_E(0)²`; `lwXE_phi_le` (from `tailW_regime1_bounds` with `ℓ ↦ min ℓ L`, since `r ≤ L` while `ℓ` may exceed `L`) is the only use of `λ²/L² ≤ 1-t`. The core `lwXE_core` runs with `u = N^{τ/16}`; `√ρ ≤ τ log N` is used at `τ/32` (for `K_n ≤ u`) and, through `lwXE_rho_poly`, as `ρ+1 ≤ N^τ` for the copied `lwXE_ev_poly` and the Ward sum. 12 helpers are copied from `AuxGraph2` (`lwXE_xiSq_nonneg` … `lwXE_num`; the five lattice ones come from `anpKey_zdistInf_tri`/`anpKey_zdistInf_sub_comm`); 15 of the 27 private `lwXE_` declarations are new (b.7). `sfT_shift_le`, `sqrt_le_add_sqrt_shift` of the probe are not introduced (b.6).
- (A) `lwMEA_assm` is the setup of `lwtermExpN_of_LWterm` for `LWMoment`; `lwMoment_holds` is applied after all introductions with `ε₁ = min(ε₀, dc/2)` and its own `c`, so the order `∀ ε₀ ∃ c ∀ 𝔠` of `LWMoment` is no obstacle. With `p = 2q'`: `lwMEA_phiB_sq_le`: `Φ_B(cr)² ≤ (2/min(c,1))^{d-2}(1+2^{d-1}) e^{√(m/ℓ_t)} 𝖳(m)²` (`λ²/L² ≤ 1-t`, `r ≤ L`); on `regA K`, `√(m/ℓ_t) ≤ √(K (log W)^{3/2})`; `lwMEA_loss`: `(C e^{√(K (log W)^{3/2})})^{q'} ≤ N^σ` eventually for every `σ > 0`; `lwMEA_prec_mono` transfers `≺`.
- Instances (b.5): `ekTTkInf` (`L=ℓ=Λ=5`, `W=25`, `g=1/2`, `t=9/10`, `D=univ`: 125 points), the near pin at `figAux` (`L=6`, `W=2`, `D` the `ℓ^∞` ball of radius 2, nonempty), `lwXiExpClaim` and `lwMomExpNoExp` (`p=2,K=6` and `p=4,K=1/2`) at the merged `sz0`, `t ≡ 1/16` (index sets nonempty at every `n`: `LWXiExp.lean:760`, `LWMomentExpA.lean:418`), `lwTail32` at `c=1` and `c=1/4`. In the X and A instances `LWInit`, `LWLoopExp` and the entry law stay hypotheses (other gates' pins); the radius `ρ0 n = log N_n` is discharged (`√ρ0 ≤ τ log N` once `log N ≥ τ^{-2}`).
## (c) Verified Mathlib names (`#check @NAME`, `S/lean/chk.lean`; one line each; the library names new relative to the merged sources that the files copy from, `names.py`, plus four more checked by the same run)
Real.exp_nat_mul : ∀ (x : ℝ) (n : ℕ), Real.exp (↑n * x) = Real.exp x ^ n
@Real.le_sqrt : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → (x ≤ √y ↔ x ^ 2 ≤ y)
@Real.log_le_rpow_div : ∀ {x ε : ℝ}, 0 ≤ x → 0 < ε → Real.log x ≤ x ^ ε / ε
@Real.mul_self_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x * √x = x
@Real.one_le_exp : ∀ {x : ℝ}, 0 ≤ x → 1 ≤ Real.exp x
Real.tendsto_log_atTop : Filter.Tendsto Real.log Filter.atTop Filter.atTop
@mul_min_of_nonneg : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] {a : R} [PosMulMono R] (b c : R), 0 ≤ a → a * min
@mul_one_div_cancel : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → a * (1 / a) = 1
@one_le_mul_of_one_le_of_one_le : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [ZeroLEOneClass M₀]
@Nat.le_self_pow : ∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
@Nat.lt_floor_add_one : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] (a : R), a < ↑⌊a⌋₊ 
@Real.sqrt_le_iff : ∀ {x y : ℝ}, √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2
@Real.log_le_log : ∀ {x y : ℝ}, 0 < x → x ≤ y → Real.log x ≤ Real.log y
@div_le_self : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b : α} [IsStrictOrderedRing α]
Names verified absent: `sfT_shift_le`, `sqrt_le_add_sqrt_shift` (0 hits in `RBM3D/`, b.6): not introduced.
## (d) Open issues and paper-delta candidates
- `T2359a` (statement difference): conjunct 2 of `claim:xi` for the exp class (`7_8:1653`, `ξ ≺ 𝖳_t(|·|∧ℓ) + W^{-D}`) is stated and proved only on `λ²/L² < 1 - t` (Amend 1, DECISIONS §163 (1)); reason: `T2359-prove-1a0.md` row 8 (for `1-t < λ²/L²` the loop zero mode `(L^d(1-t))^{-1}` is not dominated by `𝖳²`).
- Not new: the shift factor `(ρ+1)^{d-2}` (`lwXE_tailT_shift`, T2348a), `regA` with a free `K` (T2348b), the radius `√ρ ≤ τ log N` and the `(log W)^{3/2}` tail `lwTail32` (T2344c), `claim:TTk` in `ℓ^∞` (T2344d). Internal, not statement differences: the class `Φ_E` at `D' = 2D` and the constants `1 + 2^{d-1}`, `1 + 𝔡⁻²`, `(2/min(c,1))^{d-2}`.
- For R3: (i) `lwMomExpNoExp_holds` is stated with `LWf` as pinned; R3 converts with `LWfD … univ = LWf` (DECISIONS §162 (2)); (ii) `lwXiExpClaim_holds` takes the radius as the hypothesis `∀ τ > 0, ∀ᶠ n, √ρ_n ≤ τ log N_n` (C4 (d)); the limit check for `ρ_n = (log N_n)^{3/2}` is (a) row 12, the instance of `LWXiExp.lean` discharges it for `ρ = log N`; (iii) `lwMomExp_step_aux` is public and unused by these files (b.7).
- Open: none blocking. No hypothesis was added, no pinned signature changed, no file outside the four was touched (b.3).
