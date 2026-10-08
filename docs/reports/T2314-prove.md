Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 02:08:55 UTC 2026

Notation: `N = sz.size n`, `n_ ≥ 2`, `p ≥ 1`, `A = 6 n_ + 20`, `κ'` = `κ/2` (flow `κ`), `V n = Unit`, `Cv = 0`. Every numerical condition is `∀ᶠ n`. File:line are on `main` (66fd97e).

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | mesh `A` (`u−u' ≤ N^{-A}`) | `6n_+20` (n_=2,3,6: 32, 38, 56) | `N^{n_}(3n_N^{2n_+7}√δ + N^{2n_+2}δ) ≤ 1` at `δ = N^{-A}` (`nqLift_arith`, NQEndFlowLift:705-755; `ξ`-closeness `:757-829`) | `A/2−(3n_+7) = 3`; value `= 3n_N^{-3}+N^{-(3n_+18)}`; at `N = 3n_+1`: 0.0175 (2), 0.009 (3), 0.0026 (6) |
| 2 | `‖Δ𝓛‖` | `3n_N^{2n_+7}√(u−u')` | `LemDecCalELip_Lloop_sub`; hyps `3n_+1 ≤ N`, `\|E\|<2`, `(η_t)⁻¹ ≤ N²` (`LemDecCalELip_env`, LemDecCalELip:751) | see 1, 3 |
| 3 | thresholds `N ≥ 3n_+1`; `(η_t)⁻¹ ≤ N²` | `c₁ = √(2κ')/2` (LemDecCalELip:751-770), `(η_t)⁻¹ = (1−t)⁻¹(Im m)⁻¹` | `1/c₁ ≤ N`, `(1−t)⁻¹ ≤ N` (from `RangeCond(ε/2)`, copy of NQEndFlowLift:939-955) | `1/c₁ = 6.32` (κ=1/10), `20` (κ=1/100): `N ≥ max(1/c₁, 3n_+1)`; instance `N = 2^21` |
| 4 | `‖Δ𝒦^{(n_)}‖` | `N^{2n_+2}\|u−u'\|` (`stKloop_lip` NQEndFlowLift:581, `k = n_`) | `2 ≤ k` (so `n_ ≥ 2` suffices; no `n_ ≥ 3`) | exponent of row 1 uses `N^{2n_+2}δ ≤ N^{-3n_-18}`; K^(2) empirical Lipschitz `3.45e-5` vs `N^6 = 8.5e37` |
| 5 | `B_u` bounds | `N⁻¹ ≤ B_u` (`cont_inv_size_le_Bctl`), `B_{u'} ≤ B_u` (`STBctl_mono`, `u<1`) | `B_u^{-n_} ≤ N^{n_}`; ratio of `B`'s not needed in the one-sided direction | instance: `N⁻¹ = 4.8e-7 ≤ B_0 = 3.1e-5 ≤ B_{1/16} = 3.3e-5` |
| 6 | `STXiLK` closeness | `STXiLK_u ≤ STXiLK_{u'} + 1` | per `(σ,a)` closeness (row 1) passes through `Finset.sup'` (`STmaxLK`, Step34Pins:56, same index set for all `u`); the leading `1` of `STXiLK` cancels; `ε n = 1` | jump `ε n = 1`; `ε ≤ ζ♯` needs `ζ♯ ≥ 1` (row 9) |
| 7 | floor net | `netSize(A+1,N) = ⌈N^{A+1}⌉+1`, `θ = s+netPt ≤ u` | `0 ≤ u−θ ≤ 1/netSize ≤ N^{-(A+1)} ≤ N^{-A}` (`nqLift_netPt_floor` :308, core `hdist`) | factor `N`; `t−s ≤ 1` since `0 ≤ s`, `t<1` |
| 8 | net cardinality / budget | `#Fin(netSize+1) = ⌈N^{A+1}⌉+2 ≤ N^{A+2}` (`card_net_le`, `N ≥ 4`); `#Unit = 1 ≤ N^0` | `C = A+1+1+Cv = A+2` (34, 40, 58); per-time input used at `D+C` (`stochDomAt_of_perTimeDomAt`, StochDomAt) | `PerTimeDomAt` is `∀ D`, so any `C` is absorbed |
| 9 | `ζ♯ = B_u^{1/6}XLK♯(n_,u) + STbootRHS 1 (XL♯ · u) (XLK♯ · u) B_s n_ p` | `≥ 1`, non-decreasing in `u∈[s,t]`, `≤ ζ` | `B_s>0`, `XL♯,XLK♯ ≥ 1` non-decreasing, exponents `−1/(4p)`, `1/2`, `1/(4p)` fixed `B_s` | at `n_=2`: `STbootRHS 1 = B_s^{-1/4}XL(3)^{1/2}XL(4)^{1/4} + XLK(1) + XL(1)+XL(2)+XL(3)` (`Icc 1 1 = {1}`; `Icc 2 1 = ∅`) |
| 10 | one-sided `hclose` | `ζ♯(u') ≤ 2ζ♯(u)` for `u' ≤ u` | from monotonicity (constant `1`) and `ζ♯ ≥ 0` | factor 2 |
| 11 | absorption in core | `N^τ − 2N^{τ/2} − 1 ≥ 0` | `N^{τ/2} ≥ 3` (`eventually_le_rpow 3`, Defs/Domination:68) | `x²−2x−1 = 2` at `x = 3` |
| 12 | diagonal → pair | bad pair `(v,u)`: `N^τζ♯(u) < Ξ̂_v` ⇒ bad diagonal pt `v` (`ζ♯(v) ≤ ζ♯(u)`, `N^τ ≥ 0`); same `τ' = τ` | `s ≤ v ≤ u ≤ t` | none lost |
| 13 | regime/threshold | `STXiRound'` and `STXiRoundPT''` both `2 ≤ n_` (QtNonzeroBoot:93, QEndB1:100) | `n_ ≥ 2`, `p ≥ 1` same | none; `𝔠_d` that of `stOeqQtRoundPT''_holds d`, unchanged by the lift |

Index-set check (envelope, bad-set inclusion): `X♯(u) = max(1, inf_{u'∈[u,t_n]} X(u'))`; `N^τX♯(u) < Ξ̂_w` gives `u' ∈ [u,t_n]` with `N^τX(u') < Ξ̂_w`, and `(w,u')` is a pair. The left sides of the pair hypotheses depend on `q.1.1` only, the right sides on `q.1.2` only (QtNonzeroBoot:93-101).

### (ii) Concrete nondegenerate instance
`d=3`, `sz0` at `n=0` (`L=4, W=32, N=2^21, lam=1/64`), `z0 0 = 1/2+iN^{-4/5}`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `C_d=1`, `s≡0`, `t≡1/16`, `n_=2`, `p=1`; controls `X(m,u) = (1+m/10)·{3 on [0,1/32), 1.5 on [1/32,3/64), 4 on [3/64,1/16]}`, `1` beyond `t` (a jump in `u`, and `X♯` differs from `X`). `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ X` stay hypotheses (other gates' pins); everything else is a number below. Command (python3, no Lean):
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2314/preflight.py`
```
G2': 3000 random step-control draws (lo=1; p in {1,4}; n_ in {2,3,6}; Bctl of sz0 n=0), 42000 envelope evaluations
  violations (a)1<=X#, (b)X#<=X, (c)X# mono, (d)envelope bad-set inclusion, (e)z#(th)<=z#(u), (f)z#<=z, (g)z#>=1, (h)bad pair=>bad diagonal pt, (i)z#(th)<=2z#(u): [0, 0, 0, 0, 0, 0, 0, 0, 0]
sup'-pass: 20000 draws, STXiLK_u <= STXiLK_u' + 1 given per-loop closeness; violations: 0
floor net (exact Fractions, N in {2^21, 3n_+1}, n_ in {2,3,6}, A=6n_+20): 12000 draws, violations of 0<=x-netPt<=1/netSize<=N^-A: 0
mesh arithmetic: N^n_(3 n_ N^(2n_+7) sqrt(delta) + N^(2n_+2) delta) at delta=N^-A  [= 3 n_ N^-3 + N^-(3n_+18)]; Bound (3n_+1) N^-3 <= 1 iff N^2 >= 3n_+1
  n_=2 A=32: A/2-(3n_+7)=3 | value at logN=1,2,3,6: ['0.006', '6.0e-6', '6.0e-9', '6.0e-18'] | at N=3n_+1=7: 0.01749 <=1: True
  n_=3 A=38: A/2-(3n_+7)=3 | value at logN=1,2,3,6: ['0.009', '9.0e-6', '9.0e-9', '9.0e-18'] | at N=3n_+1=10: 0.009 <=1: True
  n_=6 A=56: A/2-(3n_+7)=3 | value at logN=1,2,3,6: ['0.018', '1.8e-5', '1.8e-8', '1.8e-17'] | at N=3n_+1=19: 0.002624 <=1: True
net: card Fin(netSize(A+1,N)+1) = ceil(N^(A+1))+2 <= N^(A+2) (card_net_le, N>=4); per-time input at D+C, C=A+2; V=Unit: card=1<=N^0
  n_=2 A=32 C=A+2=34: ceil(N^(A+1))+2 <= N^(A+2) at N=2^21: True
  n_=3 A=38 C=A+2=40: ceil(N^(A+1))+2 <= N^(A+2) at N=2^21: True
  n_=6 A=56 C=A+2=58: ceil(N^(A+1))+2 <= N^(A+2) at N=2^21: True
instance: d=3 L=4 W=32 N=2097152 (=2^21) lam=1/64 z0=1/2+i*8.764e-06 E=lemE(z0)=0.500000 lemT=0.999990949>=t=1/16: True
  kappa=eps=dd=1/10, c=1/6, C_d=1, s=0, t=1/16, n_=2, p=1;  Bandwidth W>=N^(1/6): True ; WO: W^(-3/2+1/10)=0.00781 <= lam=0.01562 <= 10: True
  |E|<=2-kappa/2: True ; (1-t)^-1=1.0667 <= N: True ; 3n_+1=7 <= N: True ; RangeCond(eps/2=1/20): N^(-19/20)=9.873e-07 <= 1-t=0.9375: True ; etaT^-1=1.1016 <= N^2: True ; 1-t>=Im z/4: True
  Bctl(0)=3.0987e-05 Bctl(t)=3.3052e-05 (Bctl(0)<=Bctl(t): True) ; N^-1=4.768e-07 <= Bctl(0): True ; 1<=Bctl^-n_<=N^n_ at u=0,t
  hclose at the instance (A=32, delta=N^-32): ||dL||+||dK|| bound = 1.4791e-31 <= Bctl(0)^2 = 9.6019e-10 : True
  n_=2: STbootRHS 1 = Bs^(-1/4) XL(3)^(1/2) XL(4)^(1/4) + XLK(1) + XL(1)+XL(2)+XL(3)  [Icc 1 1={1}; Icc 2 1 empty], Bs^(-1/4)=13.4031
  X#(.,m=1) at u=[0, 0.0156, 0.025, 0.0312, 0.0469, 0.0625]: [1.65, 1.65, 1.65, 1.65, 4.4, 4.4] ; X(.,1): [3.3, 3.3, 3.3, 1.65, 4.4, 4.4]
  zeta#(u) = [29.9, 29.901, 29.901, 29.902, 66.674, 66.677] ; zeta(u) = [52.63, 52.632, 52.633, 29.902, 66.674, 66.677]
  zeta# nondecreasing: True ; zeta# <= zeta: True ; zeta# >= 1: True ; zeta#(u')<=2 zeta#(u) (u'<=u): True
  diagonal->pair at the instance, c=2.071: bad pairs (v<=u) whose diagonal point v is not bad: 0
  diagonal->pair at the instance, c=2.000: bad pairs (v<=u) whose diagonal point v is not bad: 0
  STPair s t (grid of 6 times): 21 pairs, diagonal pairs (q1=q2): 6, off-diagonal (q1<q2): 15
  empirical Lipschitz of K^(2) on [0,1/16] (sup over sigma,a): 3.4521e-05 <= N^(2k+2)=N^6=8.507e+37: True
  env crossover flow kappa=0.1, kappa'=kappa/2=0.05: c1=sqrt(2 kappa')/2=0.158114, 1/c1=6.32456 <= N, and 3n_+1 <= N: N >= max(1/c1, 3n_+1)
  env crossover flow kappa=0.01, kappa'=kappa/2=0.005: c1=sqrt(2 kappa')/2=0.05, 1/c1=20.0 <= N, and 3n_+1 <= N: N >= max(1/c1, 3n_+1)
limits along sz0 (L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6, z0=1/2+i N^(-4/5)): n | N_n | (1-t)^-1<=N | 3n_+1<=N | RangeCond | |E|<=2-k/2 | WO | Bandw(W>=N^(1/6)) 
  n=0        N=2.0972e+6 True True True True True True
  n=1        N=5.4976e+11 True True True True True True
  n=10       N=1.166e+25 True True True True True True
  n=1000     N=2.1352e+60 True True True True True True
  n=1000000  N=2.0972e+114 True True True True True True
  columns: (1-t)^-1<=N | 3n_+1<=N | RangeCond | |E|<=2-kappa/2 | WO | Bandwidth
  N_n = 128^3 (n+1)^18 -> infinity (SizeTendsto)
```
External limits: the hypotheses entering from outside the lift (`SizeTendsto`, `Bandwidth 𝔠`, `WO 𝔡`, `RangeCond(ε/2)`, `|E_n| ≤ 2−κ/2`, `(1−t)⁻¹ ≤ N`, `3n_+1 ≤ N`) are the `Admissible` / `v3_premises_of_stFlow` (Green/Pins:1049) outputs; the limit table above evaluates each along `sz0` at `n = 0, 1, 10, 10^3, 10^6` (all True, `N_n = 128^3(n+1)^18 → ∞`). In the same script row `n_=2`: `3n_+1 = 7 ≤ N = 2^21`, `hclose` bound `1.5e-31 ≤ B_0^{2} = 9.6e-10`. The data of the instance are the merged `sz0`, `z0`, `flow_z0` (the ticket's instance data).

### Verdicts
- **Targets 1 (private envelope/right-side/core/arith copies, `lo = 1`): PASS.** `ζ♯` monotone / `≤ ζ` / `≥ 1` / `ζ♯(u') ≤ 2ζ♯(u)`: 0 violations in 3000 random step-control draws, `n_ ∈ {2,3,6}`, `p ∈ {1,4}`; the `lo = 1` list at `n_ = 2` is non-empty (`XLK(1)`).
- **Target 1 new gluing (`qtLift_diag_PT`, `qtLift_xiLK_close`, `qtLift_diag_to_pair`): PASS.** Diagonal pair `(w,w)` is an `STPair`; `sup'` pass: 0 violations in 20000 draws; bad pair ⇒ bad diagonal point: 0 violations in 3000 draws and at the instance.
- **Targets 2, 3 (`stXiRoundQt_holds`, `stOeqQt'_holds`): PASS.** The hypothesis set is satisfiable at once (instance above); `𝔠_d` kept; no `n_ ≥ 3` needed.
- **§29/§45 O2:** (1) `0 ≤ s`, `s<t ≤ lemT` from `STIngR`; `t<1`, `(1−t)⁻¹ ≤ N`, `|E|<2−κ/2` from `v3_premises_of_stFlow`: PASS. (2) regime `STCaseI` only inside `stOeqQtRoundPT''_holds`: PASS. (3) no `L^d ≤ W^K`, `st_window`, `STConStInd` in the lift: PASS. (4) all conditions `∀ᶠ n`: PASS. (5) `Prec` over `STPair` from `PrecPT` via the `N^{-C}`-net (3_5:1764): PASS. (6) `𝔠_d` from the per-time pin: PASS. (7) scale `N = sz.size n`: PASS.
- **G5 (mesh, ξ-modulus, net budget): PASS** (rows 1, 3, 7, 8, 11; every row `≤ 1` already at `N = 3n_+1`).
- **G6 (one-sided core, diagonal): PASS** (floor net: 12000 exact draws, 0 violations; `V = Unit`, `Cv = 0`).
- Correction to the T2258 table (not a failure here): the env constant is `c₁ = √(2κ')/2` with `κ' = κ/2` (LemDecCalELip:751-770), so the crossover is `1/c₁ = 6.32` (κ=1/10), `20` (κ=1/100), not `8.9`/`29`.
- Observation: the `(i)` column of the violation list (`ζ♯(th) ≤ 2ζ♯(u)`) follows from (e) and (g); it is listed as the one-sided `hclose` consequence.

## (b) Script output — Thu Oct  8 02:24:11 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2314`, branch `t/T2314`, commits `3967cc9 2cc4707 8baecf2 ` on base `66fd97e`; `1098` lines in `RBM3D/Induction/QtXiRoundLift.lean`.

```
$ lake build RBM3D.Induction.QtXiRoundLift   (tail; own-file lines only; the upstream replays print their own warnings)
ℹ [3905/3905] Built RBM3D.Induction.QtXiRoundLift (6.6s)
info: RBM3D/Induction/QtXiRoundLift.lean:1095:0: 'RBM.Ind.stXiRoundQt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtXiRoundLift.lean:1096:0: 'RBM.Ind.stOeqQt'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtXiRoundLift.lean:1097:0: 'RBM.Ind.QtXiRoundLiftInst.inst_OeqQt'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtXiRoundLift.lean:1098:0: 'RBM.Ind.QtXiRoundLiftInst.inst_RoundQt' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3905 jobs).
exit 0
```

### Targets, extracted from the file
```
$ grep -n -E "^theorem (stXiRoundQt_holds|stOeqQt'_holds|inst_OeqQt'|inst_RoundQt)" RBM3D/Induction/QtXiRoundLift.lean
714:theorem stXiRoundQt_holds : ∀ d : ℕ, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t) := by
736:theorem stOeqQt'_holds : ∀ d : ℕ, STOeqQt' d := fun d => stXiBootR_of_round d STCaseI (stXiRoundQt_holds d)
756:theorem inst_OeqQt' : InstIngConcl (fun sz E s t => STXiBoot' sz E s t) sz0 z0 sInst tInst 1 :=
761:theorem inst_RoundQt : InstIngConcl (fun sz E s t => STXiRound' sz E s t) sz0 z0 sInst tInst 1 :=
$ python3 -I shapes.py   (private helper shapes of the check file section 3 vs the in-file `example … := @qtLift_…`)
T2314_diag_PT <-> qtLift_diag_PT (example @qtLift_diag_PT): whitespace-normalized text identical
T2314_diag_to_pair <-> qtLift_diag_to_pair (example @qtLift_diag_to_pair): whitespace-normalized text identical
T2314_xiLK_close <-> qtLift_xiLK_close (example @qtLift_xiLK_close): whitespace-normalized text identical
T2314_lift <-> qtLift_lift (example @qtLift_lift): whitespace-normalized text identical
T2314_zeta_mono <-> qtLift_zeta_mono (example @qtLift_zeta_mono): whitespace-normalized text identical
$ lake env lean T2314-check-scratch.lean   (check file + 4 examples: T2314_stXiRoundQt_holds, T2314_stOeqQt'_holds, T2314_consumer_I, T2314_PT''_imp_PT')
example : T2314_stXiRoundQt_holds := @RBM.Ind.stXiRoundQt_holds
example : T2314_stOeqQt'_holds := @RBM.Ind.stOeqQt'_holds
example : T2314_consumer_I := fun d h => RBM.Ind.stXiBootR_of_round d STCaseI h
example : T2314_PT''_imp_PT' := fun sz E s t h n_ p hn => h n_ p (by omega)
exit 0
```

### Compiled nonempty instances (namespace `RBM.Ind.QtXiRoundLiftInst`, file lines)
```
752: /-- **(1) stOeqQt'_holds at the data**: the uniform R2* pin at (sz0, z0, s ≡ 0, t ≡ 1/16), C_d = 1: th
760: /-- **(2) stXiRoundQt_holds at the data**: the same for the round pin STXiRound'. -/
765: /-- **(3) (1) with the conclusion applied** at n_ = 2, p = 1, XL ≡ XLK ≡ 1: STKbound, STKward come
784: /-- **(3′) (2) with the conclusion applied** at n_ = 3, p = 1: the round, with the current-length summand
801: /-- **(3″) the same at the new boundary n_ = 2** (the case 3 ≤ n_ of STXiRoundPT' does not reach it). 
824: /-- **(4) qtLift_xiLK_close at the data, unfolded at a size index** (sz0, E = STflowE z0, [s, t] = [0, 1/
844: /-- **(4) the good event is nonempty at every size index**: the zero configuration lies in contGood. -/
847: /-- **(5) qtLift_core_below at the data**: P = seqP sz0, size = sz0.size, window [0, 1/16], V n = Unit
873: /-- **(5) the floor net point and the right-side monotonicity at numbers**: the floor net point of x = 1/2 at 
888: /-- **(6) the envelope at the instance window [0, 1/16]**: the constant control 1 has envelope 1 at every 
925: /-- **(6) the envelope lemmas at X = 2 + |u|, t ≡ 1/16**: X♯ ≤ X, monotone on u ≤ t, and the pai
942: /-- **(6) the envelope of a decreasing jump control**: X(m, n, u) = 4 on u < 1/32, 3 for u ≥ 1/32 has 
956: /-- **(6) the right side ζ♯ at the envelope controls, at the data**: for the decreasing jump control X(m, 
979: /-- **(7) the diagonal and pair index sets are nonempty**: at every size index the pairs (w, u) with w < u e
991: /-- **(7) the diagonal restriction and the propagation at the data**: the deterministic per-time domination
1018: /-- **(7) the lift qtLift_lift applied at the data** (the per-time pin STXiRoundPT'' of T2313 is the one hyp
1028: /-- **(8) the pinned statements** (check file T2314-check.lean, §3): stXiRoundQt_holds and stOeqQt'_holds
examples in the file: 39; in the instance namespace: 31
```

### Registry pre-check and the branch diff
```
$ lake env lean reg_after.lean   (import RBM3D; import RBM3D.Induction.QtXiRoundLift; #assert_rbm_axioms; Axioms.lean of this branch)
  reg_before.lean = the same without the QtXiRoundLift import, run before the registry edit was built (Axioms olean of main)
[before] exit 0
axiom audit: 8979 theorems, 2923 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 148 (borrowed 1, owed 89, structural 41, refuted 6, superseded 11).
registry: 2 borrowed + 140 owed + 105 structural + 7 refuted + 12 superseded; 118 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
   STOeqQt' in the owed list: 1
[after] exit 0
axiom audit: 8983 theorems, 2923 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 148 (borrowed 1, owed 89, structural 41, refuted 6, superseded 11).
registry: 2 borrowed + 139 owed + 105 structural + 7 refuted + 12 superseded; 117 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
   STOeqQt' in the owed list: 0
$ git diff --stat main...t/T2314
 RBM3D/Induction/QtXiRoundLift.lean | 1098 ++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean             |    3 +-
 2 files changed, 1099 insertions(+), 2 deletions(-)
$ git diff --patience main...t/T2314 | grep -c '^-[^-]'   -> 2   (the registry deletion and the comment line)
-   `RBM.Gauss.Sizes.STOeqQt', -- `lem:STOeq_Qt`, R2* (DECISIONS §80): S3-18b; S3-18b2 via `stXi
-   `RBM.Gauss.Sizes.STXiRound', -- one round of `(am;asoi222)` with the current-length control 
+   `RBM.Gauss.Sizes.STXiRound', -- one round of `(am;asoi222)` with the current-length control 
```

### Hygiene, name clashes, copies
```
$ grep -n 'sorry\|admit\|native_decide\|^axiom\|maxHeartbeats\|open private\|_private' RBM3D/Induction/QtXiRoundLift.lean   -> 0 hits
$ grep -n 'dDriftNonAltN\|budgetNonAltN\|dDriftAltQN\|alt_hdriftQN\|dFlowQN_levelM\|GoodSetN\|GridGoodNConcl' RBM3D/Induction/QtXiRoundLift.lean   -> 0 hits
$ grep -n -F 'RBM1D' / 'RBM2D' RBM3D/Induction/QtXiRoundLift.lean   -> 1 hit(s) (header: no port); RBM1D/RBM2D diff-stat: not applicable, nothing ported or touched
public declarations: 4 (stXiRoundQt_holds stOeqQt'_holds inst_OeqQt' inst_RoundQt )
private declarations: 23 (prefix qtLift_, plus inst_htN in the instance namespace)
$ git grep -n -F <name> ae94fa7 -- RBM3D RBM3D.lean   (name-clash grep on main)
  [stXiRoundQt_holds] 
  [stOeqQt'_holds] ae94fa7:RBM3D/Induction/QtNonzeroBoot.lean:579:round only (paper-delta candidate `T2304a`).  Case (i) consumer;
  [QtXiRoundLiftInst] 
  [inst_OeqQt'] 
  [inst_RoundQt] 
  [qtLift_] 
  [inst_htN] 
$ git log -1 --format=%h -- RBM3D/Induction/NQEndFlowLift.lean   -> d0484be  (source of the copies, lines as in the ticket)
$ diff <(NQEndFlowLift.lean ranges 73-124,133-248,267-416,703-750,752-827,849-863 with nqLift_->qtLift_) RBM3D/Induction/QtXiRoundLift.lean | grep '^<'   (the 13 source lines that differ: 8 `lo = 2`, 5 docstring)
< `B` is needed): for `s_n ≤ θ ≤ u ≤ t_n < 1`, the right side of `STNQConclPT''` at the envelope controls
<       STbootRHS 2 (fun m => nqFlowSharp t XL m n θ) (fun m => nqFlowSharp t XLK m n θ)
<       STbootRHS 2 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
<   refine add_le_add ?_ (qtLift_bootRHS_mono 2 _ _ _ _ _ n_ p hBs
<       STbootRHS 2 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
<       STbootRHS 2 (fun m => XL m n u) (fun m => XLK m n u) (sz.Bctl n (s n)) n_ p := by
<   refine add_le_add ?_ (qtLift_bootRHS_mono 2 _ _ _ _ _ n_ p hBs
<       STbootRHS 2 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
<   have := qtLift_bootRHS_one_le (lo := 2) (XL := fun m => nqFlowSharp t XL m n u)
< /-- **The floor net point** (`T2258_netPt_floor`; the witness of `exists_netPt_close`, `Domination.lean:171`, at
< /-- **The one-sided net lift** (`T2258_core_below`): the merged `cont_core` (`ContinuityNet.lean:142`) with the
< /-- **The mesh arithmetic** (`G5` of the ticket): for `δ ≤ N^{-(6 n_ + 20)}` and `N ≥ 3 n_ + 1`,
< /-- **The `ξ` closeness on `contGood`** (one-sided, for `s ≤ u' ≤ u ≤ t`, `u - u' ≤ N^{-(6 n_ + 20)}`):
```

### Narrative (stage 1b)
- Result: `Induction/QtXiRoundLift.lean` (new, 1098 lines; ticket estimate 720 / 850 / 1000, stop rule 1200: not reached) proves `RBM.Ind.stXiRoundQt_holds` (`:714`) and `RBM.Ind.stOeqQt'_holds` (`:736`), with the pinned types (scratch check above, exit 0). `STOeqQt'` leaves `owedProps` (owed 140 → 139; found 148 → 148). The full `lake build` and the root import are the hub's merge step and were not run here.
- Copies (private, prefix `qtLift_`, from `NQEndFlowLift.lean` at d0484be, line ranges in the diff above): envelope `:74-124`, right side `:133-248` with `STbootRHS 2 ↦ 1` at the eight listed lines, one-sided core `:268-416`, `qtLift_arith` `:705`, `qtLift_xi_close` `:757`, `qtLift_prec_of_le_right` `:851`, `qtLift_flowLam` `:859`. `nqFlowSharp` and `stKloop_lip` are reused (public). No port from RBM1D/RBM2D.
- New text: `qtLift_xiLK_close` (`:582`; the per-loop closeness through `Finset.sup'_le` / `Finset.le_sup'`, the leading `1` cancels), `qtLift_diag_PT` (`:611`), `qtLift_diag_to_pair` (`:621`), `qtLift_lift` (`:640`; the model `nqLift_lift`, with `V = Unit`, `Cv = 0`, `ε ≡ 1`, `A = 6 n_ + 20`, `Ξ = contGood`), the two theorems (`:714`, `:736`).
- The lift uses `STXiRoundPT''` at every `2 ≤ n_`; `1 ≤ n_` for `qtLift_zeta_one_le` is `by omega` from `2 ≤ n_`; `stOeqQtRoundPT'_holds` is not used (example `T2314_PT''_imp_PT'`, last line of the instance namespace). `𝔠_d` is that of `stOeqQtRoundPT''_holds d`, kept.
- Deviation from the ticket's text of step 5, not from any pin: `StochDomAt.of_subset` (`Defs/StochDomAt.lean:321-325`) has one index type `U` for both sides (the variable line `{U : ℕ → Type*} … {ξ ζ … ξ₁ … ζ₁ … : ∀ l, U l → Ω → ℝ}`), so it cannot pass from `TimeIcc s t n × Unit` to `STPair s t n`. `qtLift_diag_to_pair` instead unfolds `StochDomAt` and uses `measure_mono` with the same `τ' = τ`: the pair-bad event at `(v, u)` is inside the diagonal-bad event at `v` because `g n v ≤ g n u`. Statement and use are as in the check file (`T2314_diag_to_pair`, text-identical).
- Instances (namespace `QtXiRoundLiftInst`, 31 examples + `inst_OeqQt'`, `inst_RoundQt`, private `inst_htN`): data `sz0, z0, flow_z0, sInst ≡ 0, tInst ≡ 1/16, C_d = 1`, `n = 0` (`N = 2^21`), as in `QEndB1Inst`. `inst_OeqQt'`/`inst_RoundQt` discharge every deterministic hypothesis through `inst_ing`; the conclusions are applied at `n_ = 2` (`STXiBoot'` and `STXiRound'`) and `n_ = 3` with `p = 1`, `XL ≡ XLK ≡ 1`; `STLK`, `STStep2Concl` and the pair controls `Ξ̂ ≺ 1` stay hypotheses of those examples (other gates' pins, as in T2313's example (6)). The lift is also applied directly (`qtLift_lift` at the data, hypothesis `STXiRoundPT''`). The `STXiLK` closeness is instantiated at `n_ = 2` (`A = 32`) from `LemDecCalELip_env`, `stKloop_lip` and `contGood`, unfolded with `.exists`. The core is applied at `V = Unit`, `ξ n (u, v) = u`, `ζ ≡ 1`, `Ξ = contGood` (the ticket allowed `ξ ≡ 0`, `Ξ ≡ univ`; the instance used is less degenerate). The envelope examples include a decreasing jump control with `X♯(0) = 3 ≠ 4 = X(0)`; the diagonal/pair index sets are shown nonempty with `q.1.1 < q.1.2` and `q.1.1 = q.1.2`.
- Section (a): read, not edited (stage 1b appended (b)-(d) below its last line); no correction needed, no `(a′)`. Its exponent table was not contradicted by anything compiled here (the mesh arithmetic `qtLift_arith` compiled at `3 n_ + 1 ≤ N` as in (a) row 1).

## (c) Verified Mathlib names used by the new text (each `#check`ed in a scratch file; none claimed absent)
- `Finset.sup'_le`, `Finset.le_sup'` (`s.sup' H f ≤ a` from `∀ b ∈ s, f b ≤ a`; `f b ≤ s.sup' _ f`).
- `div_le_iff₀` (`0 < c → (b / c ≤ a ↔ b ≤ a * c)`), `div_le_div_of_nonneg_right` (`a ≤ b → 0 ≤ c → a / c ≤ b / c`).
- `MeasureTheory.measure_mono`, `Finset.mem_univ`, `Real.rpow_nonneg`, `lt_of_le_of_lt`, `mul_le_mul_of_nonneg_left`, `Nat.cast_nonneg`.
- `Filter.Eventually.and`, `Filter.Eventually.exists` (instances (4); `(hnum.and hK).exists`).
- The copies use the names of `NQEndFlowLift.lean` (compiled there and here).

## (d) Open issues and paper-delta candidates
- `T2314a` (as the ticket expected): the uniform-in-`(v,u)` form of `(am;asoi222)` from the per-time one. The paper's "standard `N^{-C}`-net argument, together with `lem_ConArg`" (`3_5:1764`) is here a one-sided floor net on the diagonal `v = u` with the monotone envelope `X♯` of the controls, the `𝒦` time modulus (`stKloop_lip`, T2258b) and the `𝓛` modulus on `contGood`, applied to the round (the self-absorbing summand `B_u^{1/6} Ξ_{n_}` present) before the deterministic bootstrap `stXiBootR_of_round`; the paper solves first (`3_5:1764`, "upon solving") and nets afterwards (T2304a: the bootstrap is deterministic in `(n, u)`, so the orders agree).
- `T2314b`: the net is taken over the diagonal only; the pair statement over `STPair s t` follows from the monotonicity of `ζ♯` in `u` (`qtLift_zeta_mono`, `qtLift_diag_to_pair`). The paper nets over the pairs.
- Open: `STXiRound'` stays owed (the registry comment now says "case (i) proved by `stXiRoundQt_holds` (T2314)"; `STIterR'` precedent). `STXiBoot'` stays owed (hypothesis of `STIterR'`). Downstream S3-25 / S3-26 consume `stOeqQt'_holds`; the regimes `STRegIterI` and `STCaseI` are reconciled there (ticket, "Downstream").
- Observation: the registry scan counts `STIngR` 3 → 4, `STXiBoot'` 7 → 8, `STXiRound'` 4 → 6 (types of the new public theorems that mention them); no new unregistered premise, `found` unchanged at 148.
