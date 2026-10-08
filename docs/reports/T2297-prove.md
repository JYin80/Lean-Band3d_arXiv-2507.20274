Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 14:59:32 UTC 2026

Restart under H136 with Amend 1 (replaces the BLOCKED section (a) of the earlier stage 1a). Notation: `nWS` = number of black waved edges (`col = false`); `D_t = lwSampleData sz n (zt E t) t (m I) (lwS sz n t) Sp`, `D'_t = {D_t with S := svarF}`; `η = etaT E t = Im z_t`; `ord = nS + 2(nW - nV)` (`ScalingOrder.lean:65`); `Ψ' := max(Φ n 0, W^{-d/2})`; `(𝔠, K0)`: `Bandwidth 𝔠` gives `N^𝔠 ≤ W`, `L^d ≤ N ≤ W^{⌈1/𝔠⌉}`.

### (i) Exponent table
| # | quantity | value / source | constraint | slack |
|---|---|---|---|---|
| 1 | engine call | `lw_localregularX : ∀ p c, 0<c → ∀ K0 d D, ∃ outsX errsX, ∀ m ≠ 0, LWLocRegConcl p m c K0 d D (outsX.map (lwEvX m)) (errsX.map (lwEvX m)) ∧ ∀ Q ∈ …, p ≤ nWS Q` (`LWEngine.lean:771-778`); `lwEvX m r` changes only `coeff` by `m^j conj(m)^j'` (`LWEngine.lean:57-58`) | lists chosen after `(p, c_eng, K0, d, D)`, before `z, n`; evaluate at `m = mE(STflowE z n)`, `m ≠ 0` | `‖m^j conj(m)^j'‖ = 1` (script, `|mE|=1`), so `‖coeff‖` of every evaluated graph is that of `r.2`: finitely many graphs, uniform in `n` |
| 2 | engine inputs | `c_eng = ε₀/2` (`Ψ_G ≤ W^{-c_eng}`), `K0 = ⌈1/𝔠⌉`, `D ≥ Kf/𝔠` | `W^{-d/2} ≤ Ψ_G ≤ W^{-c_eng}` for `errs` (conjunct 2); `Ψ_G = N^τ Φ0 ≤ N^τ W^{-ε₀}`, `N^τ ≤ W^{τ/𝔠}` | holds for `τ ≤ 𝔠ε₀/2`; larger `τ` is weaker (`Prec` monotone in `τ`). Instance `𝔠=0.1`: `K0=10`, `D ≥ 33.3` |
| 3 | S1: `nWS(Q) ≥ p` on `outs ++ errs` | engine conjunct (`lw_nWS_ge`, `LWEngine.lean:605`; start graph has `p` black edges, `lwEngine_fxy_nWS`) | `E|LWf|^p = Σ t^{nWS-p} E Q.val D'_t`, `t^{nWS-p} ≤ 1` | `nWS-p ≥ 0`, 0 at start |
| 4 | homogeneity / bridge | `Q.val {D with S:=sS} = s^{nWS} Q.val D`; `fxyVal D_t = t·LWf`; `(fxyPowGraph p).val D_t = t^p|LWf|^p` (script H); negative control `nWS=p-1` gives `val/t^p ~ 1/t` | exact | exact |
| 5 | `t = 0` | `z_0 = E+m`, `G_0 = m`, `STGM = 0`, `LWf = 0` (script I, last check) | pointwise in `n` | exact |
| 6 | `ord(Q)` | `≥ 2p`; `≥ 3p` if `Q.ext 0 ≠ Q.ext 1` (`lw_localregular` conjunct 6, in `LWLocRegConcl`) | `Ψ`-power `ord-p ≥ p` | `ord-2p ≥ 0` |
| 7 | `ord - auxOrd` | `(nS-|molSolid|) + 2(nW-nV+nM) ≥ 0` (`counters_le` `LWSizeClaim.lean:1040`; `molSolid_length_le` `AuxGraph.lean:124`; `auxOrd = ord⟨|molSolid|,0,nM,0,0,0⟩`, `AuxGraph.lean:86`) | exponent of `Ψ_G = N^τ Φ0` in `GtoAG` is `≥ 0` | loss `N^{τ(ord-auxOrd)}`, finite list |
| 8 | `(W^d)^{nM}` | `GtoAG` factor against `(W^d η)^{-nM}` of `lwAnp_holds` | cancels | exactly 0 |
| 9 | net power, `𝓜_x≠𝓜_y` | `Ψ^{(ord-auxOrd)+(ordN-p)}`, `ordN = auxOrd` (`lwAuxNested_holds`) `= Φ0^{ord-p}`; `η^{-nM}Φ0^{ord-p}Φ(c_G r)^p ≤ (η^{-1}Φ0Φ(c_G r))^p` (ratio `η^{p-nM}Φ0^{ord-2p} ≤ 1`, `nM ≤ p`, `η ≤ 1`) | `nM ≤ p`, `ord ≥ 2p` | tight at `nM=p, ord=2p` (ratio 1, script I) |
| 10 | the pin's `c` (quantified before `𝔠`) | take `c := 1`. `c_G` of `lwAnp_holds` per `Γa` (finite class; `Γa` from `lwAuxNested_holds` at `lwEvX 1 r`, `auxVal`/`nM`/`molOf` do not read `coeff`) | `Φ(c_G r) ≤ K_G Φ(r)`, `K_G = max(C₁ c_G^{-C₂}, Cc(1/c_G))` (`LWPsiRel`, `c_G ≤ 1`) | constant for fixed `(𝔠, sz)` (the lists depend on `𝔠` through `K0, D`), absorbed by `N^τ`; script I `c_G ∈ {0.5,0.1,0.01}` |
| 11 | floor `R ≥ N^{-Kf}` | `R ≥ (C₃^{-2}Cc(2)^{-1}C₁^{-1}L^{-C₂}W^{-d}η^{-1})^p`, `Kf = p(1+C₂/d)` (`W^{-d} ≥ N^{-1}`, `L^{C₂} ≤ N^{C₂/d}`, `zdistInf ≤ L/2`) | `hfloor` of `lwExpTerm_prec_integral` (`LWExpTerm.lean:143`) | `p=2,d=3,C₂=2`: `Kf = 10/3`; instance `R_min = 2.9e-10 ≥ N^{-Kf} = 1e-70` |
| 12 | envelope `‖Q.val D_t‖ ≤ N^{Kenv}` | `‖G_t‖ ≤ η⁻¹`; `η_t ≥ Im z_{lemT z} = √lemT·Im z ≥ Im z/(1+|z|)` (`Semicircle.lean:270`, `(2.37)`; script I) `≥ N^{-1+ε}/4`; entries of `S, Sp, M` bounded by constants; sum over `nV` internal indices | `henv` of the upgrade; `Kenv` depends on the finite list only | `Kenv` is any finite number |
| 13 | far-regime tail | `GtoAG`/`scalemole` with `r = (log W)²`: `e^{-c_S r/2}` against `W^{-D'}`, `D'` large; `(L^d)^{nM} ≤ W^{K0 p}` inside `scalingSize` | `c_S (log W)²/2 ≥ (pK0+D')log W` | holds for `log W ≥ 2(pK0+D')/c_S`; asymptotic (script I, last rows) |
| 14 | `S` decay at `D'_t` | `lwSpOf_decay_E` (`LWSizeClaim.lean:461`): `(C, c_S)` independent of `t'<1`, so `‖svarF‖ ≤ C W^{-d}e^{-c_S d_B}` by `t'→1⁻`; `Sp` is the `D_t` one | same `(C, c_S)` | exact |
| 15 | **F2: near pairs** (`lwBdist ≤ K*r`, `K* = 2 + max nV` over the finite list, `r=(log W)²`; `zdistInf ≤ zdistD = lwBdist`) | max bound `|f| ≺ η⁻¹Ψ'²` (`7_8:62-66`: `|Σ_β S_{αβ}Ǧ_{ββ}| ≤ max_a|tr(Ǧ E_a)| ≺ Ψ'²` as row sums of `S^{(B)}` are 1; Cauchy–Schwarz + Ward `Σ_α|G_{xα}|² = Im G_{xx}/η`, `Im G_{xx} ≤ 2`); then `p`-th power and the upgrade (rows 11-12); no expansion at near pairs | needs `STGavLGEX sz (STflowE z) t ε₀` (unconditional: `stGbEXP_holds hd`, `.2.2`, `Green/GbEXP.lean:811`; `STGbEXPav` `Induction/Defs.lean:322`) at `Ψ'` | see rows 16-17 |
| 16 | `Ψ'` hypotheses of `STGavLGEX` | window `W^{-d/2} ≤ Ψ' ≤ W^{-ε₀}` (`Φ0 ≤ W^{-ε₀}` by `LWClass`; `W^{-d/2} ≤ W^{-ε₀}` from `LWWindow`); `STGM ≺ W^{-ε₀}` = `LWInit`.1; `STmaxLoop2 ≺ Ψ'²`: `LWLoop2` gives `𝓛^{(2)}_{(a,b)} ≺ Φ(|a-b|)² ≤ Φ0²` (antitone), sup over `|U| = L^{2d} ≤ N²` pairs by union bound (the pin's `Ψ` of `LWInit` has no relation to `Φ`, hence `Ψ'`) | `Ψ' ≤ max(1,C₃)Φ0` | exact (script I) |
| 17 | near vs pin RHS | `η⁻¹Ψ'² ≤ η⁻¹ max(1,C₃)² Φ0 Φ0`, `Φ0 ≤ Cc(2) C₁ max(1, c_ν K* r)^{C₂} Φ(c_ν K* r)` (`LWPsiRel`, `c_ν = 1`) | loss `max(1,C₃)²Cc(2)C₁(K*(log W)²)^{C₂}`, a polylog | `log(loss)/log N → 0`: 0.316 (`k=10`), 0.0150 (`k=1000`), 2e-4 (`k=10^5`), absorbed by `N^τ` `∀τ` |
| 18 | far pairs, `𝓜_x=𝓜_y` outputs | `lwScalemole_holds`: `≤ e^{-c_S r/2} sizeConst·scalingSize`, valid when `lwBdist > card(E⊕I)·r`, implied by `> K*r`; row 13 | tail `≤ W^{-D'}` | as row 13 |
| 19 | `errs` | `scalingSize ≤ W^{-D}` (engine conjunct 2) | `W^{-D} ≤ N^{-Kf}` since `W ≥ N^𝔠` | `D ≥ Kf/𝔠 = 33.3` at `𝔠 = 0.1`; `W^{-D} = 4.6e-134 ≤ 1e-70` |

### (ii) Concrete instance
`SP=`; command `python3 inst.py` (script I; `d=3,p=2,κ=1/2,ε=𝔡=ε₀=0.1,𝔠=0.1,W=10^4,L=1000,λ=1/2,z=0.5i,t=1/2,Ψ=W^{-1/4},Φ(r)=Ψ/(1+r),C₁=C₂=2,C₃=1,Cc(C)=1+C`; `LWInit`, `LWLoop2` are premises of the pin, only `Ψ, ε₀` enter the arithmetic; `L=1000` makes both near (`≤ 509`) and far (`> 509`, torus `ℓ¹`-diameter 1500) pairs exist):
```
d=3 p=2 W=10000 L=1000 N=(WL)^d=1.000e+21 lam=0.5 z=0.5j lemE=-0 lemT=0.60961 t=0.5
OK  d>=3, p even 
OK  STFlow: |Re z|<=2-kappa, N^(-1+eps)<=Im z<=1 N^(-1+eps)=1.26e-19
OK  Bandwidth N^frakc<=W N^frakc=125.9
OK  WO: W^(-d/2+frakd)<=lam<=1/frakd 2.51e-06<=0.5<=10
OK  0<=t<=lemT(z)<1 
OK  |mE|=1 (so |m^j conj(m)^j'|=1) |mE|=1.000000000000
OK  (2.37) z_{lemT(z)} = sqrt(lemT)*z, so Im z_t >= sqrt(lemT) Im z >= Im z/(1+|z|) for t<=lemT z_T=0.3903882032022076j, sqrt(T0)=0.7808>=1/(1+|z|)=0.6667
OK  eta_t = Im z_t, eta_t<=1, ||G_t||<=1/eta_t<=N (envelope exponent) 1/eta_t(T0)=2.562 N=1.00e+21
OK  LWWindow W^(-d/2)<=Psi<=W^(-eps0) 1.0e-06<=0.1<=0.398
OK  LWClass 0<Phi<=W^-eps0, W^(-d/2)<=C3*Phi(0) 
OK  LWPsiRel antitone, (eq:Psi) Cc, C1,C2>1 
-- limit along W_k=2^k (LWInit/LWLoop2 enter only through Psi=W^-1/4, eps0=0.1, d/2=1.5):
   k=10: W^-eps0/Psi=2.828e+00 (->inf), Psi/W^(-d/2)=5.793e+03 (->inf)
   k=40: W^-eps0/Psi=6.400e+01 (->inf), Psi/W^(-d/2)=1.126e+15 (->inf)
   k=80: W^-eps0/Psi=4.096e+03 (->inf), Psi/W^(-d/2)=1.268e+30 (->inf)
== F2: max bound with Psi' = max(Phi(0), W^(-d/2)) (STGavLGEX window, 7_8:62-66)
OK  W^(-d/2)<=Psi'<=W^(-eps0) (STGavLGEX window) Psi'=0.1
OK  Psi' <= max(1,C3)*Phi(0) 
OK  union count |U|=L^(2d) <= N^2 (STmaxLoop2 = sup over (a,b) of LWLoop2 terms, each <= Phi(|a-b|)^2 <= Phi(0)^2) L^2d=1.00e+18
-- near regime: |a-b|_1 <= K*(log W)^2, K=card(E+I)=2+nV (nV=4 for the start graph); pin RHS=(eta^-1 Phi(0) Phi(c r))^p, c=1
   (log W)^2=84.8, near radius K r=509.0, torus l1-diameter d*L/2=1500  -> near and far pairs both exist: True
   max over near r of Psi'^2/(Phi(0)Phi(r)) = 509.0 <= max(1,C3)^2 Cc(2) C1 max(1,K r)^C2 = 1554377.4: True
   this ratio is polylog in W; N^tau absorbs it for every tau>0 (asymptotic): log(ratio)/log N along W_k=2^k, L=1000:
   k=10: log(ratio bound)/log N = 0.3160
   k=40: log(ratio bound)/log N = 0.1796
   k=160: log(ratio bound)/log N = 0.0685
   k=1000: log(ratio bound)/log N = 0.0150
   k=100000: log(ratio bound)/log N = 0.0002
== c := 1 in the pin; lwAnp gives c_G (any c_G>0) per graph: Phi(c_G r)/Phi(r) <= max(C1 (1/c_G)^C2, Cc(1/c_G)) (constant, fixed list)
   c_G=0.5: max_r Phi(c_G r)/Phi(r)=2.00 <= 8.00: True
   c_G=0.1: max_r Phi(c_G r)/Phi(r)=9.94 <= 200.00: True
   c_G=0.01: max_r Phi(c_G r)/Phi(r)=93.81 <= 20000.00: True
== exponent chain, p=2 (ord>=2p, ord>=3p if ext0!=ext1), B=eta^-nM Psi^(ord-p) Phi(c r)^p  vs  R=(eta^-1 Psi Phi(c r))^p, Psi=Phi(0), eta=eta_t
   max B/R over nM<=p, ord>=2p: 1.0000  (=eta^(p-nM) Psi^(ord-2p) <= 1; =1 at nM=p, ord=2p)
== floor and errs: R >= (C3^-2 Cc(2)^-1 C1^-1 (L)^-C2 W^-d eta^-1)^p >= N^-Kf (Kf=p(1+C2/d)); errs: W^-D <= N^-Kf needs D>=Kf/frakc; L^d<=W^K0, K0=ceil(1/frakc)
OK  min over all pairs of R vs N^-Kf Rmin=2.912e-10 N^-Kf=1.000e-70
OK  L^d<=W^K0 K0=10: L^d=1.0e+09<=W^K0=1.0e+40
   Kf=3.333, K0=10, Dmin=Kf/frakc=33.3; W^-Dmin=4.64e-134 <= N^-Kf: True
== t=0: G_0=(0-z_0)^-1=m, z_0=E+m, so STGM=0, LWf=0: True
== far-regime tail (asymptotic): e^{-c_S r/2}, r=(log W)^2, vs W^-D': ratio of exponents (c_S r/2)/(D' log W)=c_S log W/(2D') -> inf, along W_k=2^k, c_S=0.05, D'=40:
   k=10: 0.004
   k=100: 0.043
   k=1000: 0.433
   k=10000: 4.332
```
`python3 hom.py` (script H: brute-force evaluator of `LGraph.val` on `Fin n`; graphs `p2Graph = fxyPowGraph 2` (`LWVocab.lean:191`), `figGraph` (`:253`), `lwSymmInstGraph` (`LWSymm.lean:2059`), transcribed):
```
== homogeneity val(D with S:=sS)=s^nWS val(D)  (s=1/3)
fxyPowGraph2=p2Graph: nWS=2 |lhs-rhs|=3.84e-15 |val|=1.635e+01
figGraph: nWS=4 |lhs-rhs|=0.00e+00 |val|=1.321e-03
mixed-colour graph: nWS=1 |lhs-rhs|=2.48e-16 |val|=8.855e-01
== negative control: p2Graph minus one black edge (nWS=1<p=2): val(D_t)/t^2 blows up as t->0
t=0.9: |val(D_t)|/t^2 = 1.7607e+00   (nWS=1)
t=0.5: |val(D_t)|/t^2 = 3.1693e+00   (nWS=1)
t=0.001: |val(D_t)|/t^2 = 1.5847e+03   (nWS=1)
== bridge fxyVal(D_t)=t*LWf and (fxyPowGraph 2).val(D_t)=t^2|LWf|^2, E=0, m=i, z_t=(1-t)i, H_t=sqrt(t)H0
t=0.001: |fxyVal(D_t)-t*LWf|=1.6e-23; |p2.val(D_t)-t^2|LWf|^2|=1.6e-30; |LWf|=3.345e-05
t=0.5: |fxyVal(D_t)-t*LWf|=0.0e+00; |p2.val(D_t)-t^2|LWf|^2|=4.0e-18; |LWf|=1.071e-01
t=0.9: |fxyVal(D_t)-t*LWf|=8.9e-16; |p2.val(D_t)-t^2|LWf|^2|=3.8e-15; |LWf|=5.445e+00
```

### Findings and verdicts
**F1 (resolved by Amend 1).** `lw_localregularX` has its lists before `m` (row 1) and the `nWS ≥ p` conjunct (row 3); the missing `m`-free finite list of the earlier report is supplied.
**F2 (route, as in Amend 1).** Near pairs use the max bound at `Ψ'` (rows 15-17), far pairs use expansion + `GtoAG`/`scalemole` (rows 7-9, 13, 18). The loss at near pairs is polylog, not absorbed into any power of `W`, only into `N^τ`.
**F3 (observation, no defect).** The pin's `∃ c` precedes `𝔠`, but `K0, D` (hence the lists and `c_G`) depend on `𝔠`. Harmless: take `c := 1`; `K_G` (row 10) is a constant for fixed `(𝔠, sz)`, absorbed by `N^τ`.
**F4 (correction of the earlier report).** `η_t ≥ Im z` is false: `z_{lemT z} = √lemT · z` (`(2.37)`), so `η_t ≥ Im z/(1+|z|)` (row 12); the envelope exponent is unchanged up to a constant.
The exponent table closes; no counterexample to `LWMoment` at `d = 3`.

- `lwMoment_val_smul` (`LWMomHomPin`): PASS (statement true, script H).
- `lwMoment_fxy_bridge` (`LWfBridgePin`): PASS (`lwS = t·svarF` by definition `LWStein.lean:998`; `Gt … true` is `lwGm` by `lwExpTerm2_Gt_eq_Gsm`, `LWExpTerm2.lean:873`; script H bridge).
- `lwMoment_holds` (`LWMomentPin`): PASS (hypotheses jointly satisfiable, script I; exponent table closes, rows 1-19).

## (b) Script output (stage 1b continuation under Amend 2; commands and verbatim output)
```
$ date -u
Thu Oct  8 19:16:05 UTC 2026
$ TZ=UTC git log --format="%h %cd %s" --date=format-local:"%H:%M UTC" 9f9d1a2..HEAD   (9f9d1a2: the commit this stage continues from)
a94212e 19:03 UTC T2297: Test/Axioms registry (LWMoment owed line deleted, LWMomentExp comment, LWMomentCtx structural)
145427e 19:01 UTC T2297: LWMoment section 10 (near pairs, lwMoment_holds), instances of the targets
$ git diff main...t/T2297 --stat
 RBM3D/Graph/LWMoment.lean | 1872 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |    4 +-
 2 files changed, 1874 insertions(+), 2 deletions(-)
$ lake build RBM3D.Graph.LWMoment 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3894 jobs).
$ lake build RBM3D.Test.Axioms 2>&1 | tail -2
Build completed successfully (2 jobs).
$ wc -l RBM3D/Graph/LWMoment.lean   (stop rule: CONTROL H134, DECISIONS §148 (5), Amend 2: stop size 2000)
    1872 RBM3D/Graph/LWMoment.lean
$ grep -c -w -e sorry -e admit -e native_decide -e axiom RBM3D/Graph/LWMoment.lean
0
$ grep -c '^theorem lwMoment_holds' RBM3D/Graph/LWMoment.lean
1
```
```
$ python3 names.py; lake env lean ax2.lean   (#print axioms of the 67 public declarations of RBM3D/Graph/LWMoment.lean, namespaces tracked by script)
lines with exactly [propext, Classical.choice, Quot.sound]: 67
lines with any other axiom set: 0
'RBM.Graph.lwMoment_val_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMoment_fxy_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwMoment_prec_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwMoment_prec_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwMoment_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean ex2.lean   (pins of check-file section 2 copied into namespace T2297Check; inst1, inst2 = the two examples of RBM3D/Graph/LWMoment.lean as named theorems)
'RBM.Graph.inst1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.inst2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwMoment_inst_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwMoment_inst_moment_endT' depends on axioms: [propext, Classical.choice, Quot.sound]
30:example : T2297Check.LWMomentPin := @RBM.Gauss.Sizes.lwMoment_holds
31:example : T2297Check.LWMomHomPin := @RBM.Graph.lwMoment_val_smul
32:example : T2297Check.LWfBridgePin := @RBM.Graph.lwMoment_fxy_bridge
```
```
$ sed -n 55,60p RBM3D/Graph/LWMoment.lean   (target 1)
/-- **Target `lwMoment_val_smul`** (`LWMomHomPin`): the value of a graph is homogeneous of degree
`n_{W,black}` in the variance matrix `S` (the coloured `S^±` edges, `M` and `G` are untouched). -/
theorem lwMoment_val_smul :
    ∀ {E I ι : Type} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
      (Γ : LGraph E I) (D : LData ι) (s : ℂ) (ℓe : E → ι),
      Γ.val { D with S := s • D.S } ℓe = s ^ (Γ.waved.countP (fun e => !e.col)) * Γ.val D ℓe := by
$ sed -n 77,84p RBM3D/Graph/LWMoment.lean   (target 2)
/-- **Target `lwMoment_fxy_bridge`** (`LWfBridgePin`): the graph `f_{xy}` at the flow data (variance
`S^{(t)} = t · svarF`) is `t` times the pinned `LWf` (variance `svarF`). -/
theorem lwMoment_fxy_bridge :
    ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ)
      (Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ω : sz.SeqΩ)
      (x y : Idx d (sz.L n) (sz.W n)),
      fxyVal (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) Sp ω) x y =
        (t : ℂ) * RBM.Gauss.Sizes.LWf sz n E t ω x y := by
$ sed -n 1785p RBM3D/Graph/LWMoment.lean   (target 3, the pin LWMoment of LWPins.lean:325 for every d, no added hypothesis)
theorem lwMoment_holds : ∀ d : ℕ, LWMoment d := by
$ sed -n '1824,1828p;1836,1839p;1851,1858p;1861,1862p;1868p' RBM3D/Graph/LWMoment.lean   (compiled nonempty instances; doc comments, namespaces and blank lines omitted)
example : (fxyPowGraph 2).val { auxGraph_instD with S := (1 / 2 : ℂ) • auxGraph_instD.S } ![0, 1] =
    (1 / 4 : ℂ) * (fxyPowGraph 2).val auxGraph_instD ![0, 1] := by
  have h := lwMoment_val_smul (fxyPowGraph 2) auxGraph_instD (1 / 2) ![0, 1]
  have hn : (fxyPowGraph 2).waved.countP (fun e => !e.col) = 2 := lwEngine_fxy_nWS 2
  rw [h, hn]; norm_num
example (ω : sz0.SeqΩ) :
    fxyVal (lwSampleData sz0 0 (zt 0 (1 / 2)) (1 / 2) (Matrix.diagonal fun _ => mE 0) (lwS sz0 0 (1 / 2))
      (lwSplus sz0 0 (1 / 2) (mE 0)) ω) 0 1 = ((1 / 2 : ℝ) : ℂ) * LWf sz0 0 0 (1 / 2) ω 0 1 :=
  lwMoment_fxy_bridge sz0 0 0 (1 / 2) (lwSplus sz0 0 (1 / 2) (mE 0)) ω 0 1
theorem lwMoment_inst_moment (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1 q.2‖ ^ 2 ∂(sz0.seqP))
        (fun n q _ => ((etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ 2) :=
  inst_LWMoment (lwMoment_holds 3) 2 (dvd_refl 2) hI hL
theorem lwMoment_inst_moment_endT (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tEnd Φ0) :
  inst_LWMoment_endT (lwMoment_holds 3) 2 (dvd_refl 2) hI hL
```
```
$ git diff main...t/T2297 -- RBM3D/Test/Axioms.lean   (registry edits: delete owed line, edit one comment, add one structural line)
@@ -149,8 +149,7 @@ def owedProps : List Name :=
-   `RBM.Gauss.Sizes.LWMoment, -- `lem:LW_moment` (`7_8:72-77`): LW-02
-   `RBM.Gauss.Sizes.LWMomentExp, -- `lem:LW_moment_exp` (`7_8:78-83`): LW-02, LW-13
+   `RBM.Gauss.Sizes.LWMomentExp, -- `lem:LW_moment_exp` (`7_8:78-83`): LW-13b
@@ -342,6 +341,7 @@ def structuralProps : List Name :=
+   `RBM.Gauss.Sizes.LWMomentCtx, -- the hypotheses of `lem:LW_moment` for one choice of the constants and sequences, bundled as the bi
$ { grep "^import RBM3D\." RBM3D.lean; echo "import RBM3D.Graph.LWMoment"; echo "import RBM3D.Test.Axioms"; echo "#assert_rbm_axioms"; } > reg2.lean   (registry pre-check; the library imports of RBM3D.lean plus LWMoment, since a failed `lake build` deleted RBM3D.olean, see below)
$ grep -c '^import' reg2.lean
380
$ lake env lean reg2.lean > reg2.out; echo "exit $?"
exit 0
$ grep -c 'Sizes.LWMoment,' reg2.out   (owed ledger lines naming LWMoment)
0
$ grep -n "LWMoment\|^axiom audit\|^premises found\|^registry:" reg2.out | cut -c1-150
1:axiom audit: 10293 theorems, 3044 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
57:  RBM.Gauss.Sizes.LWMomentExp: 1 [no certificate]
135:premises found by scanning: 140 (borrowed 1, owed 78, structural 42, refuted 6, superseded 13).
136:registry: 2 borrowed + 126 owed + 107 structural + 7 refuted + 14 superseded; 116 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ lake build 2>&1 | grep -n "^error"   (full build in the worktree; the root RBM3D.lean has no import of LWMoment before the hub adds it at merge)
3894:error: RBM3D.lean:381:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
3899:error: build failed
error: RBM3D.lean:381:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Gauss.Sizes.LWMoment]
```
```
$ bash clash.sh   (every public name of names2.txt + 2 private ones, grep -rw over RBM3D/ of the worktree and of the main worktree, outside LWMoment.lean)
  LWMomentCtx: worktree 1, main 0
RBM3D/Test/Axioms.lean:344:   `RBM.Gauss.Sizes.LWMomentCtx, -- the hypotheses of `lem:LW_m
total hits outside RBM3D/Graph/LWMoment.lean: worktree RBM3D/ 1, main worktree RBM3D/ 0
hits in docs/tickets/T2296.md: 0
$ grep -rn "LWMoment\|LW_moment" ../RBM2D ../RBM1D --include="*.lean" | wc -l   (no port: no RBM1D/RBM2D diff-stat)
0
$ public declarations with line numbers (names.py, decls2.txt): 67
57 lwMoment_val_smul; 79 lwMoment_fxy_bridge; 112 lwMoment_prec_of_whp; 126 lwMoment_sum_det; 160 LWMomentCtx; 175 lwMoment_flow_facts; 179 
lwMoment_size_tendsto; 183 lwMoment_eta_lower; 190 lwMoment_etaT_le_one; 208 lwMoment_D; 211 lwMoment_Dt_eq; 219 lwMoment_pval_smul; 229 
lwMoment_pval_evX; 244 lwMoment_norm_list_sum_le; 252 lwMoment_pow_conj; 258 lwMoment_expand; 343 lwMoment_decay; 380 lwMoment_scalingSize_le; 409 
lwMoment_phi_facts; 473 lwMoment_tail; 508 lwMoment_zdistInf_le; 514 lwMoment_floor; 612 lwMoment_expC_nonneg; 615 lwMoment_Gt_true_eq; 620 
lwMoment_norm_Gt_le; 628 lwMoment_entries; 644 lwMoment_pval_claim; 673 lwMoment_env; 725 lwMoment_R; 731 lwMoment_Psi_facts; 770 lwMoment_psiAll; 
774 lwMoment_entry_whp; 781 lwMoment_Wneg_le; 810 lwMoment_L_le_W; 827 lwMoment_prec_err; 875 lwMoment_tail_le; 896 lwMoment_auxVal_smul; 911 
lwMoment_ext_mol; 925 lwMoment_prec_scale; 998 lwMoment_anp_arith; 1034 lwMoment_prec_anp; 1233 LWMomFar; 1237 lwMoment_evX_one; 1241 
lwMoment_LWf_zero; 1252 lwMoment_prec_int; 1266 lwMoment_prec_far_r; 1303 lwMoment_prec_far; 1369 lwMoment_avgErr_sum; 1401 lwMoment_row_le; 1437 
lwMoment_ward_col; 1447 lwMoment_ward_row; 1461 lwMoment_CS; 1492 lwMoment_f_le; 1546 LWMomNear; 1551 lwMoment_Psi'; 1554 lwMoment_Psi'_facts; 1566 
lwMoment_maxLoop2_prec; 1586 lwMoment_avg_whp; 1595 lwMoment_fxyVal_D; 1610 lwMoment_near_arith; 1630 lwMoment_rad; 1652 lwMoment_prec_near_pre; 1748 
lwMoment_fxyPow_val; 1759 lwMoment_prec_near; 1785 lwMoment_holds; 1851 lwMoment_inst_moment; 1861 lwMoment_inst_moment_endT; 
```

### Narrative (stage 1b continuation under CONTROL H137 and Amend 2; the first command of the stage printed Thu Oct  8 18:53:22 UTC 2026)
**Verdict: all three targets proved (`lwMoment_val_smul`, `lwMoment_fxy_bridge`, `lwMoment_holds`), 1872 lines (stop size 2000); ready for the audit.**
- (R1) near pairs, stochastic part (`LWMoment.lean:1540-1778`): `LWMomNear` (block distance `≤ K (log W)²`); `lwMoment_Psi'` = `max(Φ n 0, W^{-d/2})` (section (a) rows 15-17);
  `lwMoment_maxLoop2_prec` (`STmaxLoop2 ≺ Ψ'²` from `LWLoop2`: the `≺` over `(a,b)` already is a supremum, `Φ(r) ≤ Φ(0) ≤ Ψ'`);
  `lwMoment_avg_whp` (`(RBM.Green.stGbEXP_holds hd).2.2`, i.e. `STGavLGEX`, at `Ψ'` with `LWInit.1`); `lwMoment_prec_near_pre` (pathwise `lwMoment_f_le` with
  `A = 2`, `μ = N^{τ₁}Ψ'²`; `Ψ' ≤ max(1,C₃)Φ(0)`; `Φ(0) ≤ Cc(2)C₁ max(1,s)^{C₂}Φ(s)`; `max(1,s)^{C₂} ≤ N^{τ₁}` for `s ≤ K(log W)²` by `lwMoment_rad`; `lwMoment_near_arith`);
  `lwMoment_prec_near` (upgrade by `lwExpTerm_prec_integral`: envelope `lwMoment_env` at `fxyPowGraph p` via `lwMoment_fxyPow_val`, floor `lwMoment_floor`).
- (R2) `lwMoment_holds` (:1785): `c := 1`; per `𝔠`: `K0 := ⌈1/𝔠⌉`, `D := (p(2+C₂)+1)/𝔠`, one call `lw_localregularX p (ε₀/2) _ K0 d D`, and `K` := the sum over `outsX ++ errsX` of
  `card(r.2.E' ⊕ r.2.I')`; the same `K` is the far radius of `lwMoment_prec_far` and the near radius of `lwMoment_prec_near` (the interface fact of Amend 2); joined by `st6_prec_det_iff`; `p = 0` apart.
- (R3) instances: `lwMoment_inst_moment`, `lwMoment_inst_moment_endT` (merged `inst_LWMoment`, `inst_LWMoment_endT`, `p = 2`); `LWInit`, `LWLoop2` stay hypotheses (owed registry lines).
  Instance (3) of the ticket (`nWS ≥ 2`) is superseded by the engine conjunct (Amend 2).
- Registry (`Test/Axioms.lean`): deleted the owed line of `LWMoment`, edited the comment of `LWMomentExp` to "LW-13b", added one `structuralProps` line for `LWMomentCtx` (the internal Prop-valued binder).
  The first pre-check run (printed 19:01:59 UTC) exited 1 with `[RBM.Gauss.Sizes.LWMomentCtx]` unclassified; after the line was added the run printed 19:02:34 UTC (`import RBM3D`, LWMoment, Axioms) exited 0.
- Full `lake build` in the worktree (19:04:14 to 19:04:25 UTC) fails only at the root `RBM3D.lean`, with `[RBM.Gauss.Sizes.LWMoment]` unproved, because `RBM3D.lean` has no `import RBM3D.Graph.LWMoment` until the hub adds it at merge
  (CLAUDE.md §3 (A) 4); afterwards `lake env lean` on a file with `import RBM3D` reported that `RBM3D.olean` does not exist in the worktree, so the final pre-check (above) uses the import lines of `RBM3D.lean`.
- `git diff 3f750b6 main --stat -- RBM3D/Test/Axioms.lean RBM3D.lean` shows `Axioms.lean | 1 -` and `RBM3D.lean | 2 ++` on main since the branch base: the registry edits apply to main's file by text.
- Section (a) stands (no verdict changes, no `(a′)`); no new mathematics beyond it; the near-regime loss is the polylog of row 17, absorbed by `N^τ`.

## (c) Verified Mathlib and project names (`#fullname` script `mn4.lean`, resolved under the file's opens; earlier ones from the previous stage)
- Mathlib present: `List.le_sum_of_mem`, `Nat.le_ceil`, `Real.mul_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Finset.sup'_le`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`,
  `Real.rpow_le_one_of_one_le_of_nonpos`, `even_iff_two_dvd`, `integral_complex_ofReal` (root), `Complex.norm_real`, `Real.norm_of_nonneg`, `pow_le_pow_left₀`; earlier: `Finset.sum_mul_sq_le_sq_mul_sq`, `Matrix.mulVec_single_one`, `Complex.conj_mul'`, `Equiv.sum_comp`, `Matrix.inv_submatrix_equiv`.
- Project names present: `RBM.Green.stGbEXP_holds`, `RBM.Graph.lwXiRad_holds`, `RBM.Gauss.zdistInf_le_zdistD`, `RBM.Gauss.Sizes.st6_prec_det_iff`, `RBM.Graph.lw_localregularX`, `RBM.Graph.fxyPowGraph_val_eq`, `RBM.Graph.fxyPowGraph_normal`,
  `RBM.Gauss.Sizes.lwExpTerm_prec_integral`, `RBM.Gauss.HighProbAt.inter`, `RBM.Gauss.Sizes.Prec.whp`, `RBM.Gauss.LWInst.inst_LWMoment`, `RBM.Gauss.LWInst.inst_LWMoment_endT`; earlier: `RBM.Green.im_green_diag`, `RBM.sum_SBR_row`, `RBM.Graph.lwEngine_fxy_nWS`.
- Verified absent (previous stage): `MeasureTheory.integral_complex_ofReal`, `RBM.im_green_diag`, `RBM.Gauss.sum_SBR_row`, `RBM.Green.lwWx_Gres_false`.

## (d) Open issues and paper-delta candidates
Open issues: none blocking. For the hub at merge: add `import RBM3D.Graph.LWMoment` after the last import line of `RBM3D.lean`; apply the registry edits to main's `Test/Axioms.lean` by text. `lwMoment_inst_moment*` keep `LWInit` and `LWLoop2`
as hypotheses (other gates' pins, owed registry lines; limit check in section (a) (ii)). `LWMomentCtx` is the one registry line added beyond the ticket's "expected none" (the ticket allows it for a new Prop-valued binder).
Difference from section (a), not an error: the Lean floor is `R ≥ N^{-p(2+C₂)}` with `D ≥ (p(2+C₂)+1)/𝔠` (`lwMoment_floor`, `lwMoment_prec_err`), cruder than rows 11 and 19; any finite `Kf` serves `lwExpTerm_prec_integral`.
Paper-delta candidates:
- `T2297a` (S1): the paper's `f_{xy}` uses `S`, the IBP expansion runs with `S^{(t)} = tS`; Lean uses homogeneity `lwMoment_val_smul`, `nWS ≥ p` (second conjunct of `lw_localregularX`) and `t ≤ 1` (`lwMoment_expand`, :258); `t = 0` apart (`lwMoment_LWf_zero`, :1241). The paper is silent; it matters for `t → 0`.
- `T2297b`: `(eq:far_ab)` is used only for the `𝓜_x = 𝓜_y` outputs at pairs with block distance `> K (log W)²` (`lwMoment_prec_scale`); the `𝓜_x ≠ 𝓜_y` outputs are bounded at every distance (`lwMoment_prec_anp`, no distance premise).
- `T2297c`: the expectation upgrade is `lwExpTerm_prec_integral` with the polynomial envelope `lwMoment_env` and floor `lwMoment_floor`, not the `N η_t^{-3}` bound of `7_8:948`; `LWInteg` is not used.
- `T2297d` (Amend 1, F2): near pairs (block distance `≤ K (log W)²`) by the max bound at `Ψ' = max(Φ n 0, W^{-d/2})` with a polylog loss (`lwMoment_f_le` :1492, `lwMoment_prec_near` :1759); `7_8:943-950` bounds every output by `lem:Anp`/`GtoAG` at every pair, and `(eq:boundfxyGinf)` (`7_8:61-66`) gives only `η⁻¹Ψ²`.
- `T2297e`: the pin's `∃ c > 0` is proved with `c = 1` (`lwMoment_holds`): `Φ(c_G s) ≤ K_G Φ(s)` by `(eq:Psi)` (`lwMoment_phi_facts`) and `K_G` is absorbed by `N^τ`; the paper's `c` need not depend on `p`.
