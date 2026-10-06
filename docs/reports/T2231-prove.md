Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 00:32:06 UTC 2026
Notation: `N=(WL)^d`, `T̂_u:=T_{u,D_u}`, `B=(1-u_k)^{-1}`, `ρ_j=(1-u_j)/(1-u_k)`, `X:=W^{2ε₀}(lam²W^d)^{-1/4}`, `c:=C+1`, `C=(3e^{(4d+1)/4})²` (`stTailtoTail_holds`, `TailtoTail.lean:584`), `C₇=18e^{8d+2}` (`TailtoTailSq.lean:948`). Scripts: Python in `<scratchpad>/T2231/` (no Lean).

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 0 | ticket script data `𝔠=1/2, d=3` | **infeasible**: `Bandwidth N^𝔠 ≤ W` is `(WL)^{3/2} ≤ W`, false for every `L ≥ 3` (script 1: False at `W=2^10, 2^20`); needs `d𝔠<1` | instance uses `sz0`: `𝔠=1/6, 𝔡=1/10` (`Sizes.lean:252-253`) | — |
| 1 | `𝔠_d` | `1/100` | `0<𝔠_d ≤ 1/100`; premise `STConStInd` unused | — |
| 2 | `ε₁`, `ε₀` | `ε₁=min(𝔡/8,1/4)`, `ε₀<ε₁` | closure needs `ε₀<𝔡/4`; `2ε₀-𝔡/2<0`; `W^{ε₀} ≤ W^{1/2}` (goodDet `hJstW`) | at `𝔡=1/10, ε₀=𝔡/9`: `0.0125-0.0111`; `2ε₀-𝔡/2=-0.0278` |
| 3 | `D₀`, `D*` | `D₀=2/𝔠+12d` (48), `D*=max(D,D₀)+2d+1` (55 at `D=1`) | `(L^dW^{6d})² ≤ W^{D₀}` from `L^d ≤ N ≤ W^{1/𝔠}` | `D*-(D+2d)=1` |
| 4 | level `D_u=D*+2log_W(1-u)` | `W^{-D_u}=(1-u)^{-2}W^{-D*}`; `D*-2d ≤ D_u ≤ D*` for `W^{-d} ≤ 1-u ≤ 1` | `hfl`: `D_u ≥ D*-2d ≥ D₀+1`; `W^{-d} ≤ lam² ≤ 1-t` (WO, STReg5III) | at `sz0`, `1-u=lam²`: `D_u=50.2`, slack `2.2` over `D₀=48` (script 1) |
| 5 | `hkell` exponent | `lemDecCalEPrec_kell` takes one fixed `D`; `D_{u_j}` depends on `n,j`: apply it at `D*`, then `W^{-D*} ≤ W^{-D_{u_j}}` (`D_u ≤ D*`, `W ≥ 1`); `u_j ≤ tt ≤ t` | the T2209 text "use `D_u`" is not literal | — |
| 6 | `D₂` (target 3) | `2D*+8/𝔠+3d+1` (168 at `sz0`) | LHS `≤ 8·16⁶ N⁸ W^{3d} W^{-D₂} ≤ 8·16⁶ W^{-2D*-1}` (`Y=2N(16N)⁶=2·16⁶N⁷`, `L^d ≤ N`, `ρ ≤ lam^{-2} ≤ W^d`, `N ≤ W^{1/𝔠}`); need `W ≥ 8·16⁶=2^{27}` (eventually: `N→∞`, `N ≤ W^{1/𝔠}`) | at `sz0` all `m`; saturated worst case: fails at `W=2^{10},2^{20}`, equality at `2^{27}` (script 2); ticket points `2^{10},2^{20}` are outside the eventual range |
| 7 | `C_tot` (`d=3`) | terms: init `4N^{τ₁}c`; LK×LK `N^{τ_g}cX`; G̃ `N^{τ_g}c[d log W+2X]`; Mart `N^{ε'+τ_g/2}[√(2C₇d)√(log W)+2√C₇ W^{3ε₀/2}(lam²W^d)^{-1/4}+√2]`; Rem+far `≤ T̂`; `C_tot=max(4c+√2+1, cd+√(2C₇d), 3c+2√C₇)=4.6157e6` | sum `≤ N^{τ}C_tot(1+log W+X)T̂` | (script 3) |
| 8 | `τ` and losses | `τ` from `pfStep5Alg_closure` at `(ε₀,C_tot)`; take `τ=𝔠ε₀/2` (`9.26e-4`): `τ_i,ε' ≤ τ/8`; `τ'≤τ_g/24` (`6τ'≤τ_g/4`, lossWG) and `D*τ' ≤ 1/2` (QW, `D_u ≤ D*`) | `N^τ ≤ W^{ε₀/2}` (Bandwidth) | `τ'=4.8e-6` vs `1/110=9.1e-3` |
| 9 | closure threshold (statement is `∀ᶠ`) | `W^{ε₀/2}C_tot(1+log W+W^{2ε₀-𝔡/2}) < W^{ε₀}` iff `log W ≥ 4266.7` (saturated Bandwidth); at `sz0`: `m ≥ e^{600}` | conclusion only; no hypothesis involves it | intrinsic size of `C₇` |
| 10 | grid, probability exponents | `D_g=max(D',2D*)+4` (ticket `+1`: label union `4L^{2d} ≤ 4N²` needs `D_g ≥ D'+3`); `D₁=D'+C+1` (`K+1 ≤ N^C`); `C₀=m+9=11` (`DifREP3.lean:2378`); `K=⌈N^{max(C_K,C_R)}⌉+1`, `C_R=2(7d+D*+13)` (178 at `sz0`): `128N^{7d+11-C_R/2} ≤ N^{-D*} ≤ W^{-D*}` | `64B⁷(R+ΔM) ≤ W^{-D*} ≤ T̂`, `B ≤ lam^{-2} ≤ W^d`, `R=N^{11}Δ^{1/2}`, `Δ ≤ 1/K`, `N^{-D_g} ≤ W^{-2D*}` (`W ≤ N`) | `N²≥128` for `N ≥ 12` |
| 11 | a priori `M` | `‖A_j‖ ≤ η⁻²+1 ≤ (16N)²+1 ≤ N³` (`N ≥ 257`): `norm_loopFine_crudeN` (`NQGood1.lean:916`, Hermitian, `ℓ=2`) and `STLKIM=loopL-KLK(KLloopOf)=loopL-STKloop` (`Step2Defs.lean:718`, `Defs.lean:64`), `‖STKloop‖ ≤ (W^d(1-u))⁻¹ ≤ 1` (`Kbound`); `η_u ≥ 1/(16N)` as in `DifREP3.lean:2359-2366` | `ΔM ≤ N^{3-C_R}` | pure bookkeeping, no new estimate |
| 12 | **consumer: `pfStep5Grid_duhamel`** | hyp. = `STGridRepNAt` conj. 1 at `m=2` (`A_j=STgAN`, `F_j=STelklkM+STegtM`, empty `Icc 3 2` sum), `Rem`,`Mart` per label (`ae_all_iff`); `u_{j+1}=u_j+Δ` is `gridTime` (`Walk.lean:70`), `Δ=(tt-s)/K ≥ 0`, `u_0=s ≥ 0`, `u_k ≤ tt ≤ t<1`; martingale sum = conj. 4 RHS argument `Ugen=UN…` by `rfl` | `|E|≤2`: `v3_premises_of_stFlow` | exact |
| 13 | **consumer: `goodDet` (18 premises, source)** | `hd` STIngR5; `hτ'`,`hτ` chosen (row 8); `hJst1`: `W^{ε₀} ≥ 1`; `hJstW`: `ε₀<1/4`; `hQW`: `lemDecCalEPrec_QW` (`D_uτ'≤1/2`, needs `hfl`); `hN1,hlam,hA,hlog`: `lemDecCalEPrec_numeric`; `hE`: `v3_premises`; `hu0`: `u_j ≥ s ≥ 0`; `hu1`: `u_j ≤ t<1`; `hlamu`: STReg5III; `hfl`: row 4; `hkell`: row 5; `hloss`: `lossWG_eventually`; `hω`: `goodStop'` (event at `D*`, `J₀=W^{D*}` from `goodProb` + target 2 transfer) with `J♯(u_j,D_{u_j}) ≤ W^{ε₀}` (induction) | all eventually, uniform in `u ∈ [s,t]` | none failed |
| 14 | **consumer: `ugenSum'`, kernel** | `ugenSum'` at `u=gridTime`, `c_j=Δ`, `D j=D_{u_j}`, `ℰ_j=F_j(H_j)`, `p_j` from goodDet bounds 1-2 (`J ≤ W^{ε₀}`, indicator ≤ 1); output `C T_{u_k,D_j}+ρ_j²W^{-D_j}`, `T_{u_k,D_j} ≤ T̂` (`tailAnti`, `D_j ≥ D_{u_k}`), `ρ_j²W^{-D_j}=W^{-D_{u_k}} ≤ T̂` (row 4). Kernel (`tailtoTailSq_kernel`, `v=u_j,w=u_k`): (H1) goodDet bound 3 (`p_j=N^{τ_g}(1-u_j)⁻¹[1+W^{3ε₀}(W^d(1-u_j))^{-1/2}]`); (H2) `Y`, `difRep2_norm_STeeM_le_N` (Hermitian, `|E|<2`, `η≥1/(16N)`); (H3) `kell` (`ellT=1` as `lam² ≤ 1-w`) | `ρ_j⁴W^{-2D_j}=(W^{-D_{u_k}})² ≤ T̂²`; `Σ_jΔ ≤ 1`, `W^{-2D*} ≤ T̂²` | — |
| 15 | **consumer: target 7 index** | `STPfConcl` index `{p : TimeIcc × (Fin 2→Bool) × (Fin 2→Zd) // lam² ≤ 1-t n}` = `PfStep5_PrecConcl` index with `Subtype.val`: `StochDomAt.precomp_param` (`StochDomAt.lean:335`), as `stLemDecCalE_holds` (`LemDecCalEPrec.lean:1637-1651`) | STReg5III gives nonempty at every `n` | — |

Truth of the pins (mathematics).
**Pin 1** true: `u=s+jΔ ≥ 0`; `u>0`: `ω'=(√u)⁻¹c`, `√u•ω'=c`; `u=0` forces `s=0` and `jΔ=0`, both sides `0`. **Pin 2** true: clauses of `lemDecCalEPrec_good` (`LemDecCalEPrec.lean:670`) are functions of `seqHflow n u ω` only (`Lloop=loopFine(seqHflow)`, `Gt=Gres(seqHflow)`, `STGM=STGMM(seqHflow)`, `gexRHS` takes `M`); `S` = intersection of finitely many measurable sets. **Pin 3** true with the `D₂` of row 6 (needs `lam²>0`, `1-w ≥ lam²>0`, `W→∞`, all from `Admissible`).
**Pin 5** true: `ε₀=min(ε₁,τ)/2`; `D_{tt} ≥ D*-2d ≥ D` as `1-tt ≥ lam² ≥ W^{-d}`; `ξ ≤ J♯T_{tt,D_{tt}} < W^{ε₀}T_{tt,D} ≤ N^τ T_{tt,D}` for each label; per section `tt` the bad event ⊆ `{N^τ<JsharpM(H_K)}`, `gridTime…K=tt`, `ST_pathP_eq_seqP`; `ST_PT_of_sections`. The pin has `d:ℕ` without `3 ≤ d`: for `d ≥ 1` `W ≤ (WL)^d`; for `d=0` `N=1`, `N^{-D'}=1` and `seqP` is a probability measure (`FineModel.lean:171`), so the bound is trivial.
**Pin 6** true: `LemDecCalELip_lift` with `V n=(Fin 2→Bool)×(Fin 2→Zd d (L n))` (`card ≤ 4N² ≤ N³`), `J≡1`, `m=0`, `R₀≡0`, `R=STtailTD`; floor `T ≥ W^{-D} ≥ N^{-D}` (`tail_ge`, `W ≤ N`); relative continuity `T(u') ≤ (1+(1-t)⁻¹|u-u'|)² T(u)` (`LemDecCalELip_relcont`) and `(1-t)⁻¹ ≤ N` (`htN`, `d ≥ 1`), `|u-u'| ≤ 1` give `≤ (1+N³√|u-u'|)T(u)`; Hölder of `STLK2` on `contGood` (`LemDecCalELip_LK2`); `|E| ≤ 2-κ/2`: `v3_premises_of_stFlow`; `0+1^0·T=T`. Same hypotheses as `stLemDecCalE_holds`.
**Pin 4** true by rows 2-14: strong induction on `k ≤ K` on the intersection of (a) good events at `j ≤ K` (probability `≤ (K+1)N^{-D₁}`), (b) initial bound `‖A_0‖ ≤ 4N^{τ₁}T_{s,D_s}` (`STDecayStrong` at `s`, `Bctl ≤ 2(W^d(1-s))⁻¹` from `Bparam=(g²+|1-t|)⁻¹+(L^d|1-t|)⁻¹`, `Params.lean:36`; `W^{-D*} ≤ W^{-D_s}`), (c) conj. 4 per label (`4L^{2d}N^{-D_g}`), (d) conj. 1, 2 a.e. Base `k=0`: `4N^{τ₁}<W^{ε₀}`. Step: `J♯(H_k) < W^{ε₀}` from `‖A_k‖ < W^{ε₀}T̂_{u_k}` (row 7, `log ρ_{0k} ≤ d log W`, `Σ_jΔ(1-u_j)^{-2} ≤ (1-u_k)⁻¹`, `Σ_jΔ(1-u_j)^{-3/2} ≤ 2(1-u_k)^{-1/2}`, `pfStep5Alg_riemann`; `W^{3ε₀/2} ≤ W^{2ε₀}`, `(lam²W^d)^{-1/2} ≤ (lam²W^d)^{-1/4}` as `lam²W^d ≥ W^{2𝔡} ≥ 1`).
**Corrections (c1)-(c3) of the ticket confirmed** (read from the merged text): (c1) `HighProbAt` has one set for all `D` (`StochDomAt.lean:82`) while `STGridRepNAt` gives `CK` after `D` (`Step2Defs.lean:817-821`); (c2) conj. 3 (`‖STeeM…i.2 i.2‖` proxy) unused; (c3) conj. 4 is `∃ k ≤ K` with random right side, so no stopping index. **New corrections (not in the ticket): `D_g=max(D',2D*)+4` (row 10), `hkell` at `D*` (row 5), instance data `𝔠=1/6` (row 0).**

### (ii) One concrete nondegenerate instance
Data: `d=3`, `sz0` (`L=4m, W=(2m)^5, lam=(2m)^{-6}, N=(WL)^3`, `m=n+1`; `n=0`: `4, 32, 1/64, 2097152`), `𝔠=1/6, 𝔡=1/10, κ=ε=1/10`, `z0`, `s≡0, t≡1/16` (`lam²=1/4096 ≤ 15/16`), `D=1`, `ε₀=𝔡/9`, grid `K≡4`, `Δ=1/64`, `tt=1/16`. External hypothesis `Admissible` (limits): `N^{1/6}=√128 m³ ≤ 32m⁵=W`; `W^{-3/2+𝔡}=(2m)^{-7.5+5𝔡} ≤ (2m)^{-6}=lam` iff `𝔡 ≤ 0.3`; `lam ≤ 10`; `N=2097152m^{18}→∞`; `lam²W³=(2m)³ ≥ 8`. Stochastic premises (`STLKU, STLmaxU, STStep2Concl,…, STDecayStrong`) are other gates' pins and stay hypotheses of the example. Script 1: `cd <scratchpad>/T2231 && python3 inst.py | grep -E "^(Admissible|ticket|eps1|D0|m=(1|22):|C=)"`
```
Admissible(1/6,1/10) violations over m<=20000 and m=10^5..10^12: 0
ticket spec c=1/2,d=3,L=3 (smallest L): N^c<=W ? [(1024, False), (1048576, False)]  (N^c=(WL)^1.5>W always)
eps1=min(dd/8,1/4)=0.01250 eps0=dd/9=0.01111 eps0<eps1:True eps0<dd/4:True 2eps0-dd/2=-0.02778 W^eps0<=W^(1/2):True
D0=2/c+12d=48  D*=max(D,D0)+2d+1=55  D*>=D+2d: True
m=1: W=32 lam^2=0.000244141 1-t=0.9375  D_u(1-u=lam^2)=50.2000 (>=D*-2d=49, >=D0=48)  D_t=54.96276 ; ln(L^dW^6d)^2=133.1 <= D_u lnW=174.0 : True ; lam^2<=1-t:True
m=22: W=1.64916e+08 lam^2=1.89919e-20 1-t=0.9375  D_u(1-u=lam^2)=50.2000 (>=D*-2d=49, >=D0=48)  D_t=54.99318 ; ln(L^dW^6d)^2=708.0 <= D_u lnW=949.8 : True ; lam^2<=1-t:True
C=(3e^((4d+1)/4))^2 = 5986.27 ; C7=3.5231e+12 ; Y/N^7 = 2*16^6 = 33554432 ; 8*16^6=2^27
```
Script 2 (target 3, `D₂=168`, worst case `v=0, w=1-lam²`): `python3 t3.py | grep -E "^D2|^m=(1|22|10000) |saturated: W=2\^(10|20|27|30)" | sed -E 's/ ; N<=W.*//'`
```
D2 = 2D*+8/c+3d+1 = 168.0
m=1 W=3.200e+01: ln LHS=-432.5 ln RHS=-381.2 LHS<=RHS:True ; proof bound ln(8*16^6 W^-2D*-1)=-366.0 >= lnLHS:True
m=22 W=1.649e+08: ln LHS=-2519.0 ln RHS=-2081.3 LHS<=RHS:True ; proof bound ln(8*16^6 W^-2D*-1)=-2081.5 >= lnLHS:True
m=10000 W=3.200e+21: ln LHS=-6649.5 ln RHS=-5446.9 LHS<=RHS:True ; proof bound ln(8*16^6 W^-2D*-1)=-5477.7 >= lnLHS:True
saturated: W=2^10: ln LHS - ln RHS = 11.78 (<=0 iff W>=2^27)
saturated: W=2^20: ln LHS - ln RHS = 4.85 (<=0 iff W>=2^27)
saturated: W=2^27: ln LHS - ln RHS = 0.00 (<=0 iff W>=2^27)
saturated: W=2^30: ln LHS - ln RHS = -2.08 (<=0 iff W>=2^27)
```
Script 3 (closure at `ε₀=𝔡/9, 𝔡=1/10`, losses of row 8): `python3 closure.py | grep -v "^eps0"`
```
C=5986.27 C7=3.5231e+12  coefficients: const=2.3952e+04 logW=4.6157e+06 X=3.7720e+06  C_tot=4.6157e+06
tau=c*eps0/2=9.259259e-04  taui<=tau/8=1.157e-04  tau'<=tau_g/24 (6tau'<=tau_g/4) = 4.823e-06 ; D*tau'<=1/2 needs tau'<=0.00909
closure holds iff log W >= 4266.7 (W >= e^4267 ~ 10^1853), Bandwidth saturated, eps0=dd/9, dd=1/10
at sz0 (actual N^tau, tau as above): closure holds iff ln m >= 599.9  (m >= e^600)
```
(`c` in script 1 is `𝔠`; in script 3 `c=𝔠` and `C_tot` uses `cc=C+1`.)

### Verdicts
- Pin 1 (target 1) PASS. Pin 2 (target 2) PASS. Pin 3 (target 3) PASS with `D₂=2D*+8/𝔠+3d+1` (eventual: `W ≥ 2^{27}`). Pin 4 (target 4) PASS (exponents close; `C_tot=4.6e6`, threshold `log W ≥ 4267` is the `∀ᶠ` of the conclusion; `D_g` must be `+4`, `hkell` at `D*`). Pin 5 (target 5) PASS (`d=0` trivial). Pin 6 (target 6) PASS. Targets 7, 8 PASS (assembly; index row 15).
- The ticket's size estimate and stop rule (above 1500 lines) are not assessed here: stage 1a excludes size estimates.
- Ticket verdict: PASS.

## (a′) Preflight corrections — Tue Oct  6 01:37:31 UTC 2026
None. No row, exponent or verdict of (a) is contradicted by the proof; the route differs from (a) only in constants (narrative item 4).

## (b) Script output — Tue Oct  6 01:37:31 UTC 2026
Paths: `F=RBM3D/Induction/PfStep5.lean` in the worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2231` (branch `t/T2231`); scratch `<scratchpad>/T2231/` (`stmts.sh`, `axioms.lean`, `registry.lean`). Stage 1b started at the first `date -u` of the session, Tue Oct  6 00:32:32 UTC 2026.
**B1 branch, size, build, axioms, hygiene**
```
$ date -u; git log --oneline -4; git diff --stat main...t/T2231; wc -l RBM3D/Induction/PfStep5.lean | cut -d" " -f1-2
Tue Oct  6 01:34:06 UTC 2026
9885f4c T2231: PfStep5: nonzero-sample instance of target 1, docstring registry sentence
9e3ba2f T2231: PfStep5: instances of targets 4-6 composed from the premises of STIngR5
f54dfa9 T2231: S5-11b Induction/PfStep5 (proves STPfStep5, STStep5III; registry lines)
b750bf3 T2197: merge BA-C1a BA/FlowPins
 RBM3D/Induction/PfStep5.lean | 2581 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |    3 +-
 2 files changed, 2582 insertions(+), 2 deletions(-)
2581 RBM3D/Induction/PfStep5.lean

$ lake build RBM3D.Induction.PfStep5 2>&1 | tail -1; lake env lean RBM3D/Induction/PfStep5.lean 2>&1 | wc -l   # 2nd: standalone elaboration, warning+error lines
Build completed successfully (3885 jobs).
       0

$ lake env lean axioms.lean | sed "s/.*depends on axioms: //" | sort | uniq -c   # one #print axioms per public theorem (8 targets, 12 instances)
  20 [propext, Classical.choice, Quot.sound]

$ grep -c "sorry\|admit\|native_decide\|^axiom" $F; grep -n "^set_option" $F; grep -cE "^(noncomputable )?(theorem|def|abbrev|structure)" $F; grep -cE "^private (noncomputable )?(theorem|def|abbrev|structure)" $F
0
60:set_option linter.style.longLine false
61:set_option linter.unusedSectionVars false
29
53
```
**B2 vocabulary and pins against the check file, the eight target theorems, the six pin bodies** (each target theorem has exactly the type of its pin; targets 7, 8 have the merged `STPfStep5`/`STStep5III`)
```
$ bash stmts.sh   # diff of the vocabulary + six pins (sections 0-1, docstrings included) against docs/tickets/checks/T2231-check.lean
diff vocabulary+pins exit: 0

$ grep -E "^theorem (pfStep5_(realize|goodMeas|farAbsorb|walk|PT_of_walk|lift)|stPfStep5_holds|stStep5III_holds) " $F | sed "s/ := by//"
theorem pfStep5_realize {d : ℕ} (sz : Sizes d) : PfStep5_realize_pin sz
theorem pfStep5_goodMeas {d : ℕ} (sz : Sizes d) : PfStep5_goodMeas_pin sz
theorem pfStep5_farAbsorb {d : ℕ} (sz : Sizes d) : PfStep5_farAbsorb_pin sz
theorem pfStep5_walk (d : ℕ) : PfStep5_walk_pin d
theorem pfStep5_PT_of_walk (d : ℕ) : PfStep5_PT_of_walk_pin d
theorem pfStep5_lift (d : ℕ) : PfStep5_lift_pin d
theorem stPfStep5_holds (d : ℕ) : STPfStep5 d
theorem stStep5III_holds (d : ℕ) : STStep5III d := ST_step5_caseIII_of_pf (stPfStep5_holds d)
$ awk "/^def PfStep5_[A-Za-z_]*_pin/{p=1} /^$/{p=0} p" $F   # the six pin bodies (each target theorem has exactly this type)
def PfStep5_realize_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz), 0 ≤ s n → s n ≤ t n →
    ∃ ω' : sz.SeqΩ, sz.seqHflow n (gridTime s t K n j) ω' = pathH sz s t K n j ω
def PfStep5_goodMeas_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E : ℕ → ℝ) (D : ℝ) (Jst : ℕ → ℝ → ℝ → ℝ) (τ' : ℝ) (n : ℕ) (u : ℝ),
    ∃ S : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), MeasurableSet S ∧
      ∀ ω : sz.SeqΩ, ω ∈ lemDecCalEPrec_good sz E D Jst τ' n u ↔ sz.seqHflow n u ω ∈ S
def PfStep5_farAbsorb_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, sz.Admissible 𝔠 𝔡 → ∀ Dst : ℝ, 0 ≤ Dst → ∃ D₂ : ℝ, 0 ≤ D₂ ∧
    ∀ᶠ n in atTop, ∀ v w : ℝ, 0 ≤ v → v ≤ w → sz.lam n ^ 2 ≤ 1 - w →
      4 * (2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6) * ((sz.L n : ℕ) : ℝ) ^ d *
          ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(2 * Dst))
def PfStep5_walk_pin (d : ℕ) : Prop :=
  STIngR5 d STReg5III (fun sz E s t => PfStep5_walkConcl sz E s t)
def PfStep5_PT_of_walk_pin (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (E s t : ℕ → ℝ), (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    STReg5III sz s t →
    (∀ᶠ n in atTop, 1 < ((sz.W n : ℕ) : ℝ) ∧ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) ≤ sz.lam n ^ 2) →
    PfStep5_walkConcl sz E s t → PfStep5_PTConcl sz E s t
def PfStep5_lift_pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
        STReg5III sz s t →
        PfStep5_PTConcl sz (STflowE z) s t → PfStep5_PrecConcl sz (STflowE z) s t
```
**B3 the compiled nonempty instances** (namespace `RBM.Gauss.PfStep5Inst`; every deterministic hypothesis is discharged; what stays a hypothesis is the output of targets 4/5 in `_PT`, `_lift`, `_Prec`, and the stochastic premises of `STIngR5`, which are inside `InstIng5Concl`)
```
$ awk "/^theorem pfStep5_inst_/{p=1} p{print} p&&/:=( by)?\$/{p=0}" $F   # the compiled instances, statements (proofs omitted)
theorem pfStep5_inst_realize :
    ∃ ω' : sz0.SeqΩ, sz0.seqHflow 0 (gridTime (fun _ => (0 : ℝ)) (fun _ => 1 / 16) (fun _ => 8) 0 3) ω' =
      pathH sz0 (fun _ => (0 : ℝ)) (fun _ => 1 / 16) (fun _ => 8) 0 3 (fun _ _ => 0) :=
theorem pfStep5_inst_realize_one :
    ∃ ω' : sz0.SeqΩ, sz0.seqHflow 0 (gridTime (fun _ => (0 : ℝ)) (fun _ => 1 / 16) (fun _ => 8) 0 3) ω' =
      pathH sz0 (fun _ => (0 : ℝ)) (fun _ => 1 / 16) (fun _ => 8) 0 3 (fun _ _ => 1) :=
theorem pfStep5_inst_goodMeas :
    ∃ S : Set (Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ), MeasurableSet S ∧
      ∀ ω : sz0.SeqΩ,
        ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 55 (fun _ _ _ => (1 : ℝ)) (1 / 10) 0 (1 / 16) ↔
          sz0.seqHflow 0 (1 / 16) ω ∈ S :=
theorem pfStep5_inst_farAbsorb :
    ∃ D₂ : ℝ, 0 ≤ D₂ ∧ ∀ᶠ n in atTop, ∀ v w : ℝ, 0 ≤ v → v ≤ w → sz0.lam n ^ 2 ≤ 1 - w →
      4 * (2 * ((sz0.size n : ℕ) : ℝ) * (16 * ((sz0.size n : ℕ) : ℝ)) ^ 6) * ((sz0.L n : ℕ) : ℝ) ^ 3 *
          ((1 - v) / (1 - w)) ^ 3 * ((sz0.W n : ℕ) : ℝ) ^ (-D₂) ≤
        ((sz0.W n : ℕ) : ℝ) ^ (-(2 * (55 : ℝ))) :=
theorem pfStep5_inst_walk :
    InstIng5Concl (fun sz E s t => PfStep5_walkConcl sz E s t) sz0 z0 sInst tInst 1 :=
theorem pfStep5_inst_PT (hw : PfStep5_walkConcl sz0 (STflowE z0) sInst tInst) :
    PfStep5_PTConcl sz0 (STflowE z0) sInst tInst :=
theorem pfStep5_inst_lift (hpt : PfStep5_PTConcl sz0 (STflowE z0) sInst tInst) :
    PfStep5_PrecConcl sz0 (STflowE z0) sInst tInst :=
theorem pfStep5_inst_Prec (hw : PfStep5_walkConcl sz0 (STflowE z0) sInst tInst) :
    PfStep5_PrecConcl sz0 (STflowE z0) sInst tInst :=
theorem pfStep5_inst_PT_of_premises :
    InstIng5Concl (fun sz E s t => PfStep5_PTConcl sz E s t) sz0 z0 sInst tInst 1 := by
theorem pfStep5_inst_Prec_of_premises :
    InstIng5Concl (fun sz E s t => PfStep5_PrecConcl sz E s t) sz0 z0 sInst tInst 1 := by
theorem pfStep5_inst_pf :
    InstIng5Concl (fun sz E s t => STPfConcl sz E s t) sz0 z0 sInst tInst 1 :=
theorem pfStep5_inst_step5III :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) sz0 z0 sInst tInst 1 :=
```
**B4 registry pre-check, full library build, name clash, ports**
```
$ date -u; lake build RBM3D.Test.Axioms | tail -1; lake env lean registry.lean > registry.out; echo "registry exit: $?"   # registry.lean: import RBM3D, import RBM3D.Induction.PfStep5, #assert_rbm_axioms
Tue Oct  6 01:34:39 UTC 2026
Build completed successfully (2 jobs).
registry exit: 0
axiom audit: 6823 theorems, 2337 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
lines of the output mentioning STPfStep5/STStep5III: 0; mentioning PfStep5:
97:  RBM.Gauss.Sizes.PfStep5_walkConcl: 3 [no certificate]

$ lake build   # with a temporary uncommitted `import RBM3D.Induction.PfStep5` after the last import of RBM3D.lean (git diff --stat: see next line; removed afterwards)
 1 file changed, 1 insertion(+)
Tue Oct  6 01:35:16 UTC 2026
lake build exit: 0
2589:info: RBM3D.lean:276:0: axiom audit: 6823 theorems, 2337 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4036 jobs).
error lines: 0
Tue Oct  6 01:35:52 UTC 2026
Updated 1 path from the index
git status entries after revert:        0

$ for x in <      30 public names>; do grep -rlF --include="*.lean" $x RBM3D RBM3D.lean | wc -l; done | sort | uniq -c   # main worktree, main at e5b944a
  30        0
files containing pfStep5_ or PfStep5_ (any helper prefix) in RBM3D/ and RBM3D.lean on main:        0
$ git log -1 --format=%h -- RBM3D/Path/Walk.lean   # the private lemmas copied from RBM3D (lines 280-316, 411-424), no RBM1D/RBM2D text:
ddf5f74
```
**Narrative (b)**
1. Delivered: targets 1-8 in the new file `F` (2581 lines; the ticket's estimate was 1050/1300/1600) with the ticket's three imports; 29 public declarations (3 vocabulary
   defs, 6 pins, 8 targets, 12 instances) and 53 `private` helpers (prefix `pfStep5_`, structure `PfStep5Num`); no `maxHeartbeats` option, no `sorry`. `Test/Axioms.lean`:
   two lines deleted (`STPfStep5`, `STStep5III`), one appended (item 7).
2. **Preflight line (0), consumer check, compiled.** (i) `pfStep5Grid_duhamel` is applied at `:998` (`pfStep5_assemble`) with `A_j b = STgAN`, `F_j = STelklkM + STegtM`,
   `Rem`, `Mart` of `STGridRepNAt` conjunct 1: `hrec` (`:1642`) unfolds `STgDriftN`, the `Σ_{l ∈ Icc 3 2}` term is empty (`:1653`); the martingale sum is conjunct 4's `UN
   … (fun i' => mSigma …)`, accepted for `Ugen` at `:1721`. (ii) `lemDecCalEPrec_goodDet` (`:1113`), premises by source: `τ`, `τ'` chosen (closure exponent, `min(τ/24,
   1/(2D*))`); `hJst1`, `hJstW` from `W^{ε₀} ≥ 1`, `ε₀ ≤ 1/2`; `hQW` `lemDecCalEPrec_QW` (`:2245`); `hE` `v3_premises_of_stFlow`; `hu0`, `hu1`, `hlamu` grid in `[s, tt]`
   and `STReg5III`; `hlam`, `hA`, `hlog`, `hN1` `lemDecCalEPrec_numeric` (`:2198`); `hfl` `pfStep5_fl` (`:1984`) with `D_u ≥ D* - 2d` (`pfStep5_perj`, `:1406`); `hkell`
   `lemDecCalEPrec_kell` at `D*` (`:2205`) with `D_u ≤ D*`; `hloss` `lemDecCalEPrec_lossWG_eventually` (`:2207`); `hω` `pfStep5Alg_goodStop'` (`:1462`) on the event of
   `goodProb` at the crude level `D*`. (iii) `pfStep5Alg_ugenSum'`: `:913` (initial term, `k = 1`), `:941` (drift, `c_j = Δ`, `D j = D_{u_j}`). (iv) `tailtoTailSq_kernel`
   at `:1353`: (H1) is the second conclusion of `pfStep5_pertime`, (H2) `difRep2_norm_STeeM_le_N` (`:1714`, `Y = 2N(16N)^6`), (H3) `lemDecCalEPrec_kell` at `D₂`
   (`:2206`); the far term is target 3. (v) target 7: the index `{_p : STIdx2 sz s t n // lam² ≤ 1 - t n}` of `STPfConcl` comes from `TimeIcc × V` by
   `StochDomAt.precomp_param` (`:2469`).
3. Route (corrections (c1)-(c3) followed): per section `tt` and exponent `D'` one grid `K n = ⌈N^{max(C_K, C_R)}⌉ + 1` (`C_K` of `STGridRepNAt` at `m = 2` with `D_g =
   max(D', 2D*) + 4`, `C_R = 2(C₀ + D* + 14)`). `pfStep5_fixedN` (`:1785`) covers the failure event of `∀ k ≤ K, J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` by the good events at the
   `K + 1` grid times (`goodMeas`, `ST_pathP_eq_seqP`), the initial bound (`STDecayStrong` at `s`), the weighted martingale tails of the labels (conjunct 4) and the null
   set of conjuncts 1, 2; off it `pfStep5_path` (`:1525`) is a strong induction on `k` (no stopping index): per time `goodStop'` and `goodDet`, then `pfStep5_assemble`
   (initial, drift, martingale by `pfStep5_mart_real`, remainder `64B⁷(R + ΔM) ≤ W^{-D*}`) and `pfStep5Alg_closure`.
4. Differences from (a), none a mistake of (a): `C_tot` (`pfStep5_Ctot`) is a sum `7c + 3 + cd + √(2C₇d) + 2√C₇`, not the max of row 7; every loss is bounded by `N^τ`
   with `ε' = τ/2` (not `τ/8`); `C_R` uses the existential `C₀` of `stGridRepN_holds` (row 10 used `C₀ = 11`); the a priori bound is `‖(𝓛-𝒦)^{(2)}‖ ≤ N³` for `N ≥ 257`
   (`pfStep5_apriori`: `norm_loopFine_crudeN`, `lemDecCalEPrec_Kbound`; row 11); `goodDet`'s `hkell` is taken at `D*` (row 5).
5. Premises: target 4 uses `STDecayStrong`, `STStep2Concl` (`.1`, `.2.1`), `STLmaxU`, `STLKU` and the regime `STReg5III`; `STKbound`, `STKward`, `STLK`, `STDecay`,
   `STStep1Loop`, `STConStInd` and `Cd` are unused (pin shape; `𝔠_d := 1/100`).
6. Target 5 covers every `d`: for `d = 0`, `N = 1` and the bound `N^{-D'} = 1` is `prob_le_one`; for `d ≥ 1`, `W ≤ N` gives `W^{ε₀} ≤ N^τ`. Target 6 is
   `lemDecCalEPrec_lift` at `m = 0`, `J ≡ 1`, `R₀ = 0`, `R = STtailTD`, floor `W^{-D} ≥ N^{-D}`: the only lift (DECISIONS §64 (4)).
7. Registry: the first pre-check run flagged `PfStep5_walkConcl` (a hypothesis of target 5, proved only under the premises of `STIngR5` by `pfStep5_walk`); per the ticket
   I appended one line to `owedProps`, at the place of the removed `STPfStep5` line (class proposed: owed; dispatcher to confirm). After that B4 shows exit 0,
   `PfStep5_walkConcl: 3` (target 5 and two instances carry it) and no line for `STPfStep5`, `STStep5III`.

## (c) Verified Mathlib names (all used in `F` and compiled: `lake build` exit 0, B1/B4)
- `Real.`: `exp_pos`, `log_le_log`, `log_nonpos`, `log_pow`, `mul_rpow`, `mul_self_sqrt`, `one_le_rpow`, `one_lt_exp_iff`, `one_lt_rpow`, `one_rpow`, `rpow_add`, `rpow_le_rpow`, `rpow_le_rpow_of_exponent_le`, `rpow_le_rpow_of_nonpos`, `rpow_mul`, `rpow_natCast`, `rpow_neg`, `rpow_neg_one`, `rpow_nonneg`, `rpow_one`, `rpow_pos_of_pos`, `sq_sqrt`, `sqrt_eq_rpow`, `sqrt_le_iff`, `sqrt_le_sqrt`, `sqrt_nonneg`, `sqrt_pos`, `sqrt_zero`.
- Order/algebra: `inv_anti₀`, `one_div_le_one_div_of_le`, `inv_le_iff_one_le_mul₀'`, `div_lt_iff₀`, `div_le_iff₀`, `div_le_div_of_nonneg_right`, `pow_le_pow_left₀`, `one_le_pow₀`, `le_self_pow₀`, `inv_le_one₀`, `mul_inv`, `abs_of_pos`, `monotone_nat_of_le_succ`, `smul_inv_smul₀`, `Nat.ceil_lt_add_one`, `Nat.le_ceil`, `Nat.strong_induction_on`, `Classical.choose`, `Classical.choose_spec`.
- Finset/measure/probability: `Finset.sup'_lt_iff`, `Finset.measurable_sup'`, `Finset.measurable_sum`, `Finset.sum_le_sum`, `Finset.sum_congr`, `Finset.sum_const`, `Finset.card_range`, `Finset.mul_sum`, `Finset.sum_range_one`, `Finset.Icc_eq_empty_of_lt`, `MeasurableSet.iUnion`, `MeasurableSet.iInter`, `measurableSet_le`, `measurableSet_lt`, `measure_mono`, `measure_union_le`, `measure_biUnion_finset_le`, `measure_iUnion_fintype_le`, `prob_le_one`, `ae_all_iff`, `ae_iff`, `ENNReal.ofReal_add`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_natCast`, `ENNReal.ofReal_le_ofReal`, `Filter.Eventually.of_forall`.
- Deprecated in this Mathlib (compiler warnings while drafting, replaced): `if_true`/`if_false` (use `ite_true`/`ite_false`), `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`), `Set.setOf_true` (use `Set.ofPred_true`). `rw [Finset.sup'_lt_iff]` fails on `ℝ` (instance mismatch of `<`): use `(Finset.sup'_lt_iff _).2`. The `show` tactic that changes the goal is flagged by the `show` linter: use `change`. Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
1. Size: `F` has 2581 lines against the ticket's estimate of 1050/1300/1600 (the ticket's stop rule concerned the 1a preflight, which did not assess size).
2. Registry class of `PfStep5_walkConcl` (appended to `owedProps`, B4): dispatcher to confirm; its count in the pre-check is 3.
3. The `∀ᶠ n` of target 4 has the intrinsic closure threshold of (a) row 9 (`log W ≥ 4267` at the saturated bandwidth): the instances therefore keep the stochastic premises of `STIngR5` as hypotheses (inside `InstIng5Concl`) and cannot witness the eventual conclusion at a finite `n`.
4. Downstream: `stStep5III_holds` (case (iii) of Step 5) is now unconditional on `STPfStep5`; the owed lines of `STPfStep5` and `STStep5III` are removed, the regime assembly (`ST_mainIndR_of_steps`) can use it.
5. Hub: add `import RBM3D.Induction.PfStep5` after the last `import` line of `RBM3D.lean` (here `import RBM3D.BA.FlowPins`, base `b750bf3`); the `Axioms.lean` hunk is `@@ -181,13 +181,12 @@` (deleted: `STStep5III`, `STPfStep5`; inserted after `STIniTermI`: `PfStep5_walkConcl`), at most an adjacent-hunk conflict: keep both deletions, keep the insertion.

Paper-delta candidates (dispatcher numbers them):
- **T2231a** `lem:pf_step5` (`3_5:2371-2383`) is proved on the grid without the continuous stopping time `T` of `(eq:def_TTT)`: conjunct 4 of `STGridRepNAt` (Azuma with random proxy, DECISIONS §7) is uniform in `k ≤ K`, so strong induction on the grid index at the level `D_{u_k}` replaces the stopping argument (`pfStep5_path`, `PfStep5_walkConcl`).
- **T2231b** the uniform-in-`u` conclusion is obtained from per-section grids (one grid per section and per probability exponent, `PfStep5_walkConcl`, `pfStep5_PT_of_walk`) and one net lift of `STLK2 ≤ N^τ T_{u,D}` (`pfStep5_lift`, floor `W^{-D}`).
- **T2231c** "sufficiently small constant `ε > 0`" (`3_5:2377`) is the explicit `ε₁ = min(𝔡/8, 1/4)` of `PfStep5_walkConcl` (the closure needs `ε₀ < 𝔡/4`, `goodDet` needs `W^{ε₀} ≤ W^{1/2}`), and the level is `D* = max(D, 2/𝔠 + 12d) + 2d + 1`.
