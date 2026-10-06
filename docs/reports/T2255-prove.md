Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 05:00:24 UTC 2026

### (i) Exponent table
Notation: `B = sz.Bctl n t = W^{-d}B_{t,0}`, `η = etaT = (1-t)Im m`, `m = mE E`, `e = (k ? 1 : 2)`, `ĝ = lam`, `Ψ = N^τ B^{1/2}`, `SP` = scratchpad `T2255/`.

| quantity | value / constraint | slack / source |
|---|---|---|
| bridge (target 2) | `S = tW^{-d}Lift(S^B)` (`lwExpTerm2_hS`), `S⁺ = W^{-d}K⁺` (`lwExpTerm2_hSp`), `Lloop5 = W^{-5d}Σ_{x,α,γ,β,y}`. `k=false`: `W^{-2d}Σ_{x,y}𝒢_xy = t²W^{-4d}Σ_{a}S^BS^BΣ_{fine}G⋯`, and `W^dΣ K S^B Lloop = W^{-4d}Σ_aS^BS^BΣ_{fine}G⋯`; `k=true`: `S⁺S = tW^{-2d}K⁺S^B`, one `t` | `t^{e}W^dΣKS^B∫Lloop = W^{-2d}Σ_{x∈[a],y∈[b]}∫𝒢_xy`; rel. err `≤ 5.6e-15` (`bridge.py`, §(ii)) |
| orientation | `tr(G E_{a₂}G E_{a₁}G E_{a₃}G E_b G^s E_a)`: `x∈[a]`, `α∈[a₂]`, `γ∈[a₁]`, `β∈[a₃]`, `y∈[b]`; `s=false`: `(G*)_{yx} = conj G_{xy}` (`SEdge.val` uses `star`); `s=true`: `G_{yx}`; first waved edge `S_{γα}` or `S⁺(γ,α)` with `K⁺(a₁,a₂)` | agrees with the edge list of `LWG5GraphPin` and the argument order of `LWExpKp`; script uses the trace form for the left side and the fine graph for the right side |
| `ord`, `auxOrd` | `ord = nS+2(nW-nV)`, `auxOrd = |molSolid|-2nM`; `ord-auxOrd = (nS-|molSolid|)+2nW-2(nV-nM) ≥ 0` | `molSolid_length_le` (AuxGraph:124), `counters_le` (LWSizeClaim:1040: `nV-nM ≤ nW`) |
| `q=0` | every `ξ ≺ Ψ`: `ξ² ≤ 2(2ρ+1)^{2d}max|𝓛^{(2)}|+W^{-d}`; `STLmax` at `k=2` (`≺ B`); `W^{-d} ≤ (ĝ²+1)B` (`STBctl_ge`); `ĝ ≤ 𝔡⁻¹` (`WO`, eventually) | `Ψ^{ord-auxOrd}Ψ^{auxOrd} = Ψ^{ord}`; `η ≤ 1` so `η⁻¹ ≥ 1` |
| `q=1` | two attached `ξ`-edges: `Σ_bξ(a,b)ξ(b,c) ≤ (Σξ²)^{1/2}(Σξ²)^{1/2}`, both orientations by `lwXiVar_symm` (AuxGraph2:160); `lwXi_ward_sum` (:507) with `A=Ψ ≤ 1`: `W^dΣ_{a₂}ξ² ≤ 4(2ρ+1)^{2d}η⁻¹+(2ρ+1)^d`; other edges `≤ Ψ` | gives `η⁻¹Ψ^{auxOrd}` up to `(2ρ+1)^{2d}`. Both attached edges at one external end: `ξ(a,b)²`, i.e. `Σξ²` directly: not a counterexample |
| `Ψ`-premises of `LWGtoAG` | `|G_{xy}|≤Ψ`, `|G_{xx}-m|≤Ψ`: `STLocalEntry` and **`localAvg1_STWB_le`** (Induction/LocalAvg1:94: `STWB sz n u K ≤ sz.Bctl n u`; its module is not in the ticket's imports); window `W^{-d/2} ≤ Ψ` iff `W^{-d} ≤ N^{2τ}B`, from `STBctl_ge` | window: `log10 W^{-3/2} = -2.26 ≤ log10Ψ = -1.61` at `n=0`, `tInst` |
| `hξ` (`(eq:Gbyxi)`) | `lwGbyXi_holds` (:1122) needs `‖G-M‖ ≺ W^{-ε₁}`: from `STLocalEntry` and `scaleFacts_R1` (ScaleFacts:193: `B ≤ 2N^{-c₁}`, `c₁ = min(2𝔠𝔡,τ')`, given `N^{-1+τ'} ≤ 1-t`; the range condition from `STFlow` as in `st5_Bctl_le_one`, Step5Kit:362); `W^d ≤ N` gives `ε₁ ≤ d c₁/2` | then `lwGbyXi_hxi` (:1160) is the `LWGtoAG` premise verbatim |
| radii | `ρ`, `R=(ρ-1)/2`, `r=R/|E⊕I|`: `|E⊕I|r ≤ R`, `2R+1 ≤ ρ` by construction; tail `e^{-cr/2}·sizeConst·size ≤ B^{ord/2}` needs `r ≥ K log N` | `ρ=(ln N)²`: tail ratio `10^{-103}` already at `n=10`; `2(2ρ+1)^{2d} ≤ N^τ` false at `log10N=366`, true at `726` (`τ=1/10`); absorbed in `≺ ∀τ` |
| `t^{nW}` | `sizeConst C K₁ = ‖c‖K₁^{nV-nM}C^{nW-(nV-nM)}` (LWSizeClaim:1098); `C = tC'`, `K₁ = C·expC`: `t`-power `nW` (`nV-nM ≤ nW`); `S`: `‖S_{xy}‖ ≤ t e W^{-d}e^{-lwBdist}` (support `≤1`, entries `≤1`) | `t<1`: `t^{nW} ≤ t^{e}` for `nW ≥ 2 ≥ e` |
| `S⁺ = O(t)` | `lwSplus_decay` (LWSizeClaim:1353) has **no factor `t`**; `S⁺ = tW^{-d}Lift(S^BΘ_{tm²})` (`lwSpOf_eq`); need `‖(S^BΘ)_{ab}‖ ≤ C'e^{-c·zdistD}` uniformly in `t∈[0,1)`: `t ≥ ½` from `lwSplus_decay` (`C/t ≤ 2C`); `t < ½` Neumann (`Theta_apply_eq_tsum`, Props4:142), `S_B^{k+1}` supported on `zdistD ≤ k+1`, entries `≤ 1`: `Σ_{k≥D-1}t^k` | `ker2.py`: worst `10.93` on the grid, `0.40` at `t=1e-3`. **One helper lemma not in the ticket's list** |
| `x=y` | `≤ W^d` pairs (`a=b`); `W^{-2d}[W^{2d}η⁻¹B^{5/2}+W^dη⁻¹B²]`; `W^{-d}B² ≤ (ĝ²+1)B³ ≤ (𝔡⁻²+1)B^{5/2}` (`STBctl_ge`, `B≤1`) | extra slack `B^{1/2}`; column `W^-3/B^.5` below (`≤ 5.3e-3`) |
| `t=0` | `k=false`: `G=mI`, 5-loop `= m⁴m^{(s)}W^{-4d}1[a₂=a₁=a₃=b=a]`, term `≤ W^{-3d}`; `k=true`: `K⁺=0` | `W^{-9} ≤ η⁻¹B^{5/2}`: 2.3 decades at `n=0`, 15 at `n=50` (`ords.py`); needs `ĝ` bounded (WO) |
| `≺→𝔼` floor | `lwExpTerm_prec_integral` (LWExpTerm:143) needs `N^{-Kf} ≤ R`: **fails for `R = t^{nW}η⁻¹B^{ord/2}`** when `t n` is tiny or 0 | apply it to `X = t^{-nW}val` (`t>0`; `R=η⁻¹B^{ord/2}`), envelope `‖X‖ ≤ N^K` from `|S|,|S⁺| ≤ Ct W^{-d}`, `‖G‖ ≤ η⁻¹`; `t=0`: graphs with `nW ≥ 1` vanish (`S=S⁺=0`), `nW=0` has no `t` |
| `LWG5Expand` (LW-14e) | `nW` under `(Oe2x)`: `oe2xR1,R2,R4,…,R8_counters` (LWGGExp:848-978) give `=,+1,+2,+1,+2,+1,+2`; `nM ≤` (R1, R2), `=` (R4-R8); `ord+1` each (`oe2xR*_ord` :1106-1153) | base `nW=2`, `nM=1` gives `nW ≥ 2`, `nM ≤ 1` provided `LGraph.partition` keeps the waved list (LW-14e checks); `ord` per case in `ords.py`; `LWAttached` of the outputs does **not** follow from the counters (LW-14e) |

### (ii) One concrete nondegenerate instance
Data: `d=3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `ĝ=(2(n+1))^{-6}`), `z0 n = 1/2+iN^{-4/5}`, `t∈{tInst=1/16, tEnd=lemT}`, `τ=1/10`. Target-3 graph (explicit normal `PGraph (Fin 2)`): ext `x,y`, internal `α`; solid `G_{xα},G_{αy},Ḡ_{xy},(G-M)_{αα}×2`; waved `S_{αα}×2`; `×`-dotted `(x,α),(α,y),(x,y)`; `nS=5,nW=2,nV=1,nM=1`, `ord=7`, `auxOrd=1`; the molecule `{α}` is attached to `G_{xα},G_{αy}`; ext molecules distinct. External pins (`LWG5Expand`, `LWExpI1K/I23K/I41K`, `STLocalEntry`, `STLmax`, `LWAvgLaw`, `STLK`, `STDecay`) stay hypotheses; the `ord` bounds of `LWG5Expand` are checked on its base graphs by `ords.py` (limit/consistency computation).
```
$ cd $SP && python3 inst.py     # mpmath, 80 digits
instance graph: nS=5 nW=2 nV=1 nM=1 ord=7 molSolid=3 auxOrd=1 ord-auxOrd=6 |E+I|=3
n N t-case | log10B | log10Psi | W^-3/2<=Psi | W^-3/(g2+1)<=B | lam<=10 | B<=1 | 1-t>=N^{-.9} | W^-3/B^.5 | log10(t^nW eta^-1 B^{ord/2})
0 2.097e+6 tInst | -4.4808 | -1.6082 | True | True | True | True | True | 0.005308 | -18.049
0 2.097e+6 tEnd | -0.76142 | 0.25145 | True | True | True | True | True | 7.333e-5 | 2.3923
1 5.498e+11 tInst | -9.002 | -3.327 | True | True | True | True | True | 2.952e-5 | -33.873
1 5.498e+11 tEnd | -1.702 | 0.32301 | True | True | True | True | True | 6.609e-9 | 3.4351
2 8.125e+14 tInst | -11.644 | -4.331 | True | True | True | True | True | 1.412e-6 | -43.12
2 8.125e+14 tEnd | -2.2497 | 0.36611 | True | True | True | True | True | 2.835e-11 | 4.0537
5 2.13e+20 tInst | -16.16 | -6.047 | True | True | True | True | True | 7.8e-9 | -58.925
5 2.13e+20 tEnd | -3.1794 | 0.44315 | True | True | True | True | True | 2.523e-15 | 5.1349
50 1.143e+37 tInst | -30.101 | -11.345 | True | True | True | True | True | 8.346e-16 | -107.72
50 1.143e+37 tEnd | -6.0088 | 0.70137 | True | True | True | True | True | 7.506e-28 | 8.6154

Eventual inequalities along sz0, t=tInst=1/16, rho=(ln N)^2, R=(rho-1)/2, r=R/|E+I|=R/3, c=1:
n  log10N  (2rho+1)^{2d}*2 <= N^{tau}?  tail=e^{-r/2}*L^{3 nM}*Psi^{nS}*W^{3(nV-nW)} vs target B^{ord/2}: log10(tail/B^{ord/2})
n=1e1 log10N=  25.067  poly<=N^tau: False (log10 poly=23.24, log10 N^tau=2.507)  log10(tail/B^(ord/2))=-103.1
n=1e4 log10N=  78.322  poly<=N^tau: False (log10 poly=29.18, log10 N^tau=7.832)  log10(tail/B^(ord/2))=-1124.1
n=1e12 log10N=  222.32  poly<=N^tau: False (log10 poly=34.62, log10 N^tau=22.23)  log10(tail/B^(ord/2))=-9335.2
n=1e20 log10N=  366.32  poly<=N^tau: False (log10 poly=37.22, log10 N^tau=36.63)  log10(tail/B^(ord/2))=-25504.0
n=1e40 log10N=  726.32  poly<=N^tau: True  (log10 poly=40.79, log10 N^tau=72.63)  log10(tail/B^(ord/2))=-1.0074e+5
n=1e80 log10N=  1446.3  poly<=N^tau: True  (log10 poly=44.38, log10 N^tau=144.6)  log10(tail/B^(ord/2))=-4.0042e+5
$ cd $SP && python3 bridge.py   # d=3, L=3, W=2 (N=216), E=0.6, one Hermitian Gaussian sample per t; left side by traces with block matrices E_a, right side by the fine graph
t=0.3: |lwSplus(direct) - W^-d Kp(blocks)|max = 2.03e-16
  12 combos (k,s in {F,T}^2, 3 block pairs incl. a=b): max rel.err = 2.56e-15, |lhs| range [7.0e-09, 2.0e-05]
t=0.9: |lwSplus(direct) - W^-d Kp(blocks)|max = 4.38e-16
  12 combos (k,s in {F,T}^2, 3 block pairs incl. a=b): max rel.err = 5.63e-15, |lhs| range [2.8e-04, 3.1e-03]
$ cd $SP && python3 ker2.py     # (iii): L=9, d=3, zdistD, c=1
grid g^2 in {1/4,1,4} x E in {0,1,1.9} x t in {1e-3,1e-2,.1,.5,.9,.99,.999}: worst sup|SB Theta_{t m^2}|e^{D1} = 10.9343
Neumann bound check (t=1/2): max_b |K_{0b}|/bound = 0.08421157131623089
g^2=0.25, E=1.9, t=1e-3: sup|SB Theta|e^D1 = 0.4002  -> sup|S^+_xy| e^D1 W^d / t = 0.4002
g^2=4.0, E=1.9, t=1e-3: sup|SB Theta|e^D1 = 0.4350  -> sup|S^+_xy| e^D1 W^d / t = 0.4350
$ cd $SP && python3 ords.py     # ord = nS+2(nW-nV) on the base graphs of B:96-108, then +1 per (Oe2x) step
case                                           ord(x!=y) ord(x=y)  #Oe2x  final(x!=y) final(x=y)  need(5/4)
(1) a=g=b, loops give m^2 (x!=y / merged)             5        4      0            5          4  True
(21) a=g!=b, m S_aa S_ab G_xa G_ab G_by conj G_xy        4        3      1            5          4  True
(22) a=g!=b, (G-M)_aa extra loop                      5        4      0            5          4  True
(4) a!=g!=b, two Oe2x steps (a, b)                    3        2      2            5          4  True
t=0 branch along sz0 (z0 n = 1/2 + i N^{-4/5}), d=3: log10(W^-9) <= log10(eta^-1 B_{0,0}^{5/2}) ?
  n= 0:  -13.5463 vs   -11.258  True
  n= 1:  -27.0927 vs  -22.5611  True
  n= 5:  -48.5632 vs  -40.4552  True
  n=50:   -90.387 vs  -75.3085  True
$ cd $SP && python3 mc2.py 400  # (iv) d=3, L=3, W=3 (N=729), g^2=1/4, E=0.6; block 4 contains x=y; x0,y0 in block 4
t=0.5 N=729 eta=0.4770 B=0.0521 (400 samples)  columns: |W^-2d sum E G|/(t^e eta^-1 B^2.5) for blocks (4,4) | (4,11) ; |E G_x0x0|/(eta^-1 B^2) ; |E G_x0y0|/(eta^-1 B^2.5) ; max MC se/bound
  k=0 s=0: 6.18e-03 | 7.58e-05 | 2.62e-03 | 1.19e-03 | se<=1.9e-04
  k=0 s=1: 8.90e-04 | 1.38e-06 | 2.27e-03 | 3.80e-04 | se<=2.0e-04
  k=1 s=0: 2.52e-03 | 3.08e-05 | 2.15e-03 | 9.75e-04 | se<=1.6e-04
  k=1 s=1: 3.65e-04 | 5.62e-07 | 1.86e-03 | 3.11e-04 | se<=1.7e-04
t=0.9 N=729 eta=0.0954 B=0.1195 (400 samples)  columns: |W^-2d sum E G|/(t^e eta^-1 B^2.5) for blocks (4,4) | (4,11) ; |E G_x0x0|/(eta^-1 B^2) ; |E G_x0y0|/(eta^-1 B^2.5) ; max MC se/bound
  k=0 s=0: 1.38e-03 | 6.54e-04 | 9.25e-04 | 1.07e-03 | se<=3.1e-04
  k=0 s=1: 4.91e-05 | 1.92e-06 | 4.76e-04 | 9.82e-05 | se<=3.1e-04
  k=1 s=0: 8.59e-04 | 4.06e-04 | 6.43e-04 | 7.35e-04 | se<=2.1e-04
  k=1 s=1: 3.06e-05 | 1.16e-06 | 3.37e-04 | 6.23e-05 | se<=2.1e-04
```
The last block is evidence only (`N=729` is far from asymptotic): all ratios are `≪ 1`, at both charges and both first edges. At `tEnd`, `n=0`, `B^{1/2}=0.42`. The limits `(2ρ+1)^6N^{-τ} → 0` and `e^{-cr/2}poly(N) ≤ N^{-D}` are not hypotheses of any target.

§29 checklist: (1) `0≤t≤lemT`, `t<1` (`st5_t_lt_one`); `t=0` separate in target 4; the bridge needs `0<t<1`, `|E|<2` (as pinned). (2) `ĝ²/L^d ≤ 1-t` carried by `LWExpG5'`, unused; targets 2, 3 and `LWG5Expand` have no boundary. (3) no `L^d ≤ W^K`; the `x=y` step uses `STBctl_ge`. (4) `∀ n` premises as in `LWExpG5'`; target 2 holds for every `n`, no `ĝ` bound used. (5) deterministic left sides (`‖∫…‖`), uniform over `(x,y)` and the fixed list. (6) `0<ĝ≤𝔡⁻¹` eventually only (`lwSplus_decay`, `STBctl_ge`, the `S⁺=O(t)` lemma), inside `Prec`. (7) scale `N = sz.size n`, control `sz.Bctl n (t n)`; `lwSampleData sz n z u M S Sp ω` with `z = zt E t`, `u = t`, `S = lwS sz n t`, `Sp = lwSplus sz n t (mE E)` (as in `LWG5DataPin`; the script's `S`, `S⁺` are these matrices, §34 order).

### Verdicts
- Target 1 (vocabulary): PASS (edge list reproduces the script's graph for both `k`, both `s`; `Ḡ_{xy} = star G_{xy}`).
- Target 2 (bridge): PASS (powers `t^e`, `W^{-2d}` confirmed to `5.6e-15`).
- Target 3 (`lwGraphPrec1`): PASS, with three steps outside the ticket's list: (a) the `S⁺ = O(t)` lemma (row `S⁺=O(t)`); (b) `hent` of `lwGbyXi_holds` needs `Bctl ≤ N^{-c₁}` (row `hξ`); (c) `≺→𝔼` must be applied to `t^{-nW}val` (row `≺→𝔼 floor`). These three steps are not in the ticket's breakdown of target 3 (dispatcher: decide whether target 3 splits). The Cauchy–Schwarz at a common external end is fine; `x=y` needs only `B ≤ 1`.
- Target 4 (assembly): PASS (rows `t=0`, `x=y`, `t^{nW}`; finite list).
- Target 5 (conditionals): PASS (`lwCutExp_of_terms` composed with target 4, then `lwTermEXP_of_cut`).
- Target 6 (instances): PASS (numbers above; the bridge instance needs no hypothesis).
- `LWG5Expand` pin (for LW-14e): not false at the base orders; `LWAttached` and `nW ≥ 2` of every output are LW-14e's obligations.

## (b) Script output — stage 1b, branch `t/T2255`, commit `ba20118`
```
$ git -C RBM3D-wt/T2255 log --oneline -1; date -u
ba20118 T2255: instance facts of the explicit graph as named theorems
Tue Oct  6 06:11:34 UTC 2026
$ lake build RBM3D.Graph.LWExpTerm3 | tail -1
exit=0
Build completed successfully (3881 jobs).
$ lake env lean pre.lean   # import RBM3D; import RBM3D.Graph.LWExpTerm3; #assert_rbm_axioms
exit=0
axiom audit: 7591 theorems, 2551 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
$ lake build   # full library, root imports unchanged (the hub adds the import at merge) | tail -1
exit=0
Build completed successfully (4058 jobs).
$ lake env lean ax.lean   # #print axioms: the 5 targets and the instances
exit=0
'RBM.Gauss.Sizes.lwExpTerm3_bridge' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwGraphPrec1' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpG5'_of_expand' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwCutExp_of_expand' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwTermEXP_of_expand' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_bridge' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_prec1' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_G5' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_cut' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_term' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_graph_order' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm3_instGraph_nM' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm3_instGraph_normal' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm3_instGraph_attached' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm3_instGraph_ext' : [propext, Classical.choice, Quot.sound]
$ lake env lean pins.lean   # check-file section 2 copied into T2255Check; Iff.rfl / rfl / @name; output lines:
exit=0
       0
```
Registry pre-check run before the registry edit (same file, `#assert_rbm_axioms`): `axiom audit: 2 premise(s) that no theorem of this development proves are in none of ... [RBM.Gauss.Sizes.LWAttached, RBM.Gauss.Sizes.LWG5Expand]`; after the edit: exit 0 (above).
`git diff --stat main...t/T2255`: `RBM3D/Graph/LWExpTerm3.lean | 2301 +`, `RBM3D/Test/Axioms.lean | 2 +` (nothing else).
```
$ bash clash.sh   # for each public name of the file: grep -rnw --include='*.lean' NAME RBM3D | grep -v LWExpTerm3.lean
LWAttached: RBM3D/Test/Axioms.lean:314:   `RBM.Gauss.Sizes.LWAttached, -- every in
lwGraphPrec1: RBM3D/Test/Axioms.lean:314:   `RBM.Gauss.Sizes.LWAttached, -- every in
LWG5Expand: RBM3D/Test/Axioms.lean:164:   `RBM.Gauss.Sizes.LWG5Expand, -- `(eq:siz
lwExpG5'_of_expand: RBM3D/Test/Axioms.lean:164:   `RBM.Gauss.Sizes.LWG5Expand, -- `(eq:siz
public names checked: 68
$ RBM1D/RBM2D diff-stat: no port (nothing was copied from RBM1D/RBM2D; none was read).
```
Every public declaration of `RBM3D/Graph/LWExpTerm3.lean` (68; `line: statement`, extracted by script `extract.py`; pins, targets and instances in full, helpers cut at 230 characters):
```
54: def LWG5Graph (k s : Bool) : LGraph (Fin 2) (Fin 3) where solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 0) (Sum.inr 1), SEdge.mk true false (Sum.inr 1) (Sum.inr 2), SEdge.mk true false (Sum.inr 2) (Sum.inl 1), if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)] waved := [WEdge.mk k true (Sum.inr 1) (Sum.inr 0), WEdge.mk false false (Sum.inr 0) (Sum.inr 2)] dotted := [] coeff := 1
62: noncomputable def LWG5Data {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) : LData (Idx d (sz.L n) (sz.W n)) := lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) (lwSplus sz n t (mE E)) ω
66: def LWAttached (P : PGraph (Fin 2)) : Prop := ∀ v : P.I', (∀ w ∈ P.g.mol (Sum.inr v), w.isRight = true) → 2 ≤ (P.g.solid.filter fun e => decide (P.g.mol e.src ≠ P.g.mol e.dst ∧ (P.g.mol e.src = P.g.mol (Sum.inr v) ∨ P.g.mol e.dst = P.g.mol (Sum.inr v)))).length
71: theorem lwExpTerm3_val_expand (k s : Bool) {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] = ∑ α, ∑ γ, ∑ β, (if k then lwSplus sz n t (mE E …
93: theorem lwExpTerm3_collapse {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B] (bl : ι → B) (c₀ : ℂ) (K SBm : B → B → ℂ) (α γ β : ι) : ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * SBm a₂ a₃ * lwExpTerm2_dw bl c₀ a₂ α * lwExpTerm …
117: theorem lwExpTerm3_move5 {A X₁ X₂ X₃ X₄ X₅ : Type*} [Fintype A] [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype X₄] [Fintype X₅] (f : A → X₁ → X₂ → X₃ → X₄ → X₅ → ℂ) : ∑ a, ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, f a x y α γ β = ∑ x, ∑ y, ∑ α, ∑ …
131: theorem lwExpTerm3_move3 {A₁ A₂ A₃ X₁ X₂ X₃ X₄ X₅ : Type*} [Fintype A₁] [Fintype A₂] [Fintype A₃] [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype X₄] [Fintype X₅] (f : A₁ → A₂ → A₃ → X₁ → X₂ → X₃ → X₄ → X₅ → ℂ) : ∑ a₁, ∑ a₂, ∑ a₃, …
147: theorem lwExpTerm3_alg {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B] (bl : ι → B) (c₀ : ℂ) (K SBm : B → B → ℂ) (a b : B) (F : ι → ι → ι → ι → ι → ℂ) : ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * SBm a₂ a₃ * (∑ x, ∑ y, ∑ α, …
175: theorem lwExpTerm3_perm {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ι → ℂ) : ∑ x, ∑ α, ∑ β, ∑ y, ∑ γ, f x α β y γ = ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, f x α β y γ :=
189: theorem lwExpTerm3_Lloop5_expand {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (s : Bool) (a₂ a₁ a₃ b a : Zd d (sz.L n)) (ω : sz.SeqΩ) : Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω = ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, lwExp …
212: theorem lwExpTerm3_dw_filter {ι B : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq B] (bl : ι → B) (c₀ : ℂ) (a b : B) (g : ι → ι → ℂ) : ∑ x, ∑ y, lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b y * g x y = c₀ ^ 2 * ∑ x ∈ Finset.u …
229: theorem lwExpTerm3_bridge_pt {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) (k s : Bool) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ) : (t : ℂ) ^ (if k then 1 else 2) * ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, …
304: theorem lwExpTerm3_BM_Gt {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ : Bool) (i j : Idx d (sz.L n) (sz.W n)) : lwExpTerm2_BM (fun ω : sz.SeqΩ => Gt sz n E t σ ω i j) :=
320: theorem lwExpTerm3_BM_val {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (k s : Bool) (x y : Idx d (sz.L n) (sz.W n)) : lwExpTerm2_BM (fun ω : sz.SeqΩ => (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y]) :=
336: def LwExpTerm3Bridge (d : ℕ) : Prop := ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool) (a b : Zd d (sz.L n)), (t : ℂ) ^ (if k then 1 else 2) * ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * ∫ ω, Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz.seqP)) = ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ * ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a), ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b), ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)
347: theorem lwExpTerm3_bridge (d : ℕ) : LwExpTerm3Bridge d :=
596: theorem lwExpTerm3_det (d : ℕ) (hd : 3 ≤ d) (L W : ℕ) [NeZero L] [NeZero W] (Γ : LGraph E I) (hN : Γ.Normal) (hnM : Γ.nM ≤ 1) (hatt : ∀ v : I, (∀ w ∈ Γ.mol (Sum.inr v), w.isRight = true) → 2 ≤ (Γ.solid.filter fun e => decide (Γ.mo …
727: theorem lwExpTerm3_Sp_decay (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ Λ → ∀ u E : ℝ, 0 ≤ u → u < 1 → |E| ≤ 2 - κ → ∀ x y : Idx d (sz.L …
809: theorem lwExpTerm3_Data_G (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : (LWG5Data sz n E t ω).G x y = Gt sz n E t true ω x y := rfl
812: theorem lwExpTerm3_Data_M (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : (LWG5Data sz n E t ω).M x y = if x = y then mE E else 0 :=
816: theorem lwExpTerm3_sizeConst_smul {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) (hΓ : Γ.nV - Γ.nM ≤ Γ.nW) (t C₁ e : ℝ) : Γ.sizeConst (t * C₁) (t * C₁ * e) = t ^ Γ.nW * Γ.sizeConst C₁ (C₁ * e …
846: theorem lwExpTerm3_entry_whp {E t : ℕ → ℝ} (hLE : STLocalEntry sz E t) {τ' : ℝ} (hτ' : 0 < τ') : sz.Whp (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (E n) (t n) ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bct …
872: theorem lwExpTerm3_hent {E t : ℕ → ℝ} (hsz : sz.SizeTendsto) (hd : 0 < d) {c₀ : ℝ} (hc₀ : 0 < c₀) (hB : ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₀)) (hLE : STLocalEntry sz E t) : Prec sz (U := fun n => Idx d …
938: theorem lwExpTerm3_xiSq_nonneg (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : 0 ≤ lwXiSq sz E t ρ n a₁ a₂ ω :=
942: theorem lwExpTerm3_xiVar_sq (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : lwXiVar sz E t ρ n a₁ a₂ ω ^ 2 = lwXiSq sz E t ρ n a₁ a₂ ω :=
954: theorem lwExpTerm3_pathwise (hd : 3 ≤ d) (P : PGraph (Fin 2)) (hN : P.g.Normal) (hnM : P.g.nM ≤ 1) (hatt : LWAttached P) (hext : ∀ a b : P.E', P.g.molOf (Sum.inl a) = P.g.molOf (Sum.inl b) → a = b) (Es ts ρs : ℕ → ℝ) (n : ℕ) (ω :  …
1051: theorem lwExpTerm3_Psi_zpow {N B τ' : ℝ} (hN : 0 < N) (hB : 0 < B) (o : ℤ) : (N ^ τ' * Real.sqrt B) ^ o = N ^ (τ' * (o : ℝ)) * B ^ ((o : ℝ) / 2) :=
1059: theorem lwExpTerm3_Q_le (Γ : LGraph E I) (d : ℕ) (W : ℕ) (hW : 0 < W) {ρ cc Ψ η : ℝ} (hρ : 0 ≤ ρ) (hcc : 1 ≤ cc) (hΨ : 0 ≤ Ψ) (hη0 : 0 < η) (hη1 : η ≤ 1) : (if Γ.nM = 1 then ((W : ℝ) ^ d) * (cc ^ 2 * (2 * (2 * ρ + 1) ^ (2 * d) * ( …
1103: theorem lwExpTerm3_size_le (Γ : LGraph E I) (d L W : ℕ) (hW : 0 < W) {N Ψ : ℝ} (hN : 1 ≤ N) (hΨ0 : 0 < Ψ) (hΨN : Ψ ≤ N) (hLN : (L : ℝ) ^ d ≤ N) (hWN : (W : ℝ) ^ d ≤ N) : Γ.scalingSize Ψ W d L ≤ N ^ (Γ.nM + Γ.nS + Γ.nV) :=
1130: theorem lwExpTerm3_arith (Γ : LGraph E I) (d L W : ℕ) (hW : 0 < W) {N B η ρ r Ψ cc K₁ K₂ τ τ' D c₁ : ℝ} (hN : 1 ≤ N) (hB0 : 0 < B) (hB1 : B ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1) (hΨ : Ψ = N ^ τ' * Real.sqrt B) (hcc : cc = N ^ τ') (hτ'0 …
1233: theorem lwExpTerm3_lwS_zero (n : ℕ) : lwS sz n 0 = 0 :=
1236: theorem lwExpTerm3_lwSplus_zero (n : ℕ) (m : ℂ) : lwSplus sz n 0 m = 0 :=
1241: theorem lwExpTerm3_val_zero (P : PGraph (Fin 2)) (hnW : P.g.nW ≠ 0) (n : ℕ) (E : ℝ) (ω : sz.SeqΩ) (ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)) : P.val (LWG5Data sz n E 0 ω) ℓe = 0 :=
1279: theorem lwExpTerm3_val_norm_le (Γ : LGraph E I) (D : LData ι) {g1 m1 s : ℝ} (hg : ∀ x y, ‖D.G x y‖ ≤ g1) (hm : ∀ x y, ‖D.M x y‖ ≤ m1) (hs : ∀ x y, ‖D.S x y‖ ≤ s) (hsp : ∀ x y, ‖D.Sp x y‖ ≤ s) (hg0 : 0 ≤ g1) (hm0 : 0 ≤ m1) (hs0 : 0 …
1333: theorem lwExpTerm3_floor {N B η : ℝ} (hN : 1 ≤ N) (hB0 : 0 < B) (hB1 : B ≤ 1) (hNB : N⁻¹ ≤ B) (hη0 : 0 < η) (hη1 : η ≤ 1) (o : ℤ) : N ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤ η⁻¹ * B ^ ((o : ℝ) / 2) :=
1363: theorem lwExpTerm3_etaT_le_one {E t : ℝ} (hE : |E| < 2) (h0 : 0 ≤ t) (_ht : t < 1) : etaT E t ≤ 1 :=
1374: theorem lwExpTerm3_X_norm_le (P : PGraph (Fin 2)) (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) {Cs : ℝ} (hCs : 0 ≤ Cs) (hS : ∀ x y, ‖lwS sz n t x y‖ ≤ t * Cs) (hSp : ∀ x y, ‖lwSplus sz n t (mE E) x y‖ ≤ t * Cs) (ω  …
1417: theorem lwExpTerm3_poly {N η cn Cw : ℝ} (hN : 2 ≤ N) (hη : η⁻¹ ≤ N) (hη0 : 0 ≤ η⁻¹) (hcn : cn ≤ N) (hCw : Cw ≤ N) (hCw0 : 0 ≤ Cw) (nV nS : ℕ) : cn * N ^ nV * ((η⁻¹ + 1) ^ nS * Cw) ≤ N ^ (nV + 2 * nS + 2) :=
1430: def LwGraphPrec1 (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → STLocalEntry sz (STflowE z) t → STLmax sz (STflowE z) t → ∀ P : PGraph (Fin 2), P.g.Normal → P.g.nM ≤ 1 → LWAttached P → (∀ a b : P.E', P.g.molOf (Sum.inl a) = P.g.molOf (Sum.inl b) → a = b) → Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n p _ => ‖∫ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![p.1, p.2] ∂(sz.seqP)‖) (fun n _ _ => (t n) ^ P.g.nW * (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.g.scalingOrder : ℝ) / 2))
1442: theorem lwGraphPrec1 (d : ℕ) : LwGraphPrec1 d :=
1666: theorem lwExpTerm3_wprod {ι B : Type*} [DecidableEq B] (bl : ι → B) (c₀ : ℂ) (a₂ a₁ a₃ b a : B) (x : ι) : lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b x * lwExpTerm2_dw bl c₀ a₂ x * lwExpTerm2_dw bl c₀ a₁ x * lwExpTerm2_dw bl c …
1675: theorem lwExpTerm3_Gt_zero {E : ℝ} (hE : |E| < 2) (ω : sz.SeqΩ) (i j : Idx d (sz.L n) (sz.W n)) : Gt sz n E 0 true ω i j = if i = j then mE E else 0 :=
1691: theorem lwExpTerm3_Gt_zero_s {E : ℝ} (hE : |E| < 2) (s : Bool) (ω : sz.SeqΩ) (i j : Idx d (sz.L n) (sz.W n)) : Gt sz n E 0 s ω i j = if i = j then mSigma E s else 0 :=
1700: theorem lwExpTerm3_Lloop5_zero {E : ℝ} (hE : |E| < 2) (s : Bool) (a₂ a₁ a₃ b a : Zd d (sz.L n)) (ω : sz.SeqΩ) : Lloop sz n E 0 ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω = if a₂ = a ∧ a₁ = a ∧ a₃ = a ∧ b = a then (mE E) ^  …
1751: theorem lwExpTerm3_list_norm_sum_le {α : Type*} (l : List α) (f : α → ℂ) (G : ℝ) (h : ∀ q ∈ l, ‖f q‖ ≤ G) : ‖(l.map f).sum‖ ≤ l.length * G :=
1763: theorem lwExpTerm3_pairsum {ι : Type*} [DecidableEq ι] (A B' : Finset ι) {M : ℕ} (hA : A.card = M) (hB : B'.card = M) (g : ι → ι → ℝ) {G₁ G₂ : ℝ} (hG₂ : 0 ≤ G₂) (hg : ∀ x y, g x y ≤ G₁ + if x = y then G₂ else 0) : ∑ x ∈ A, ∑ y ∈ B …
1781: def LWG5Expand (d : ℕ) : Prop := ∃ Ls : Bool → Bool → List (ℕ × PGraph (Fin 2)), (∀ k s, ∀ q ∈ Ls k s, q.2.g.Normal ∧ q.2.g.nM ≤ 1 ∧ 2 ≤ q.2.g.nW ∧ LWAttached q.2 ∧ (∀ a b : q.2.E', q.2.g.molOf (Sum.inl a) = q.2.g.molOf (Sum.inl b) → a = b) ∧ (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder) ∧ ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool) (x y : Idx d (sz.L n) (sz.W n)), ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) = ((Ls k s).map fun q => (mE E) ^ q.1 * ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum
1797: theorem lwExpTerm3_val_ext_ne (P : PGraph (Fin 2)) (h : P.ext 0 = P.ext 1) {x y : Idx d (sz.L n) (sz.W n)} (hxy : x ≠ y) (D : LData (Idx d (sz.L n) (sz.W n))) : P.val D ![x, y] = 0 :=
1809: theorem lwExpTerm3_graph_pair_bound (P : PGraph (Fin 2)) {e : ℕ} (he : e ≤ 2) (hnW : 2 ≤ P.g.nW) (hord : (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder) {t N B η τ' : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hN : 1 ≤ N) (hB0 …
1859: theorem lwExpTerm3_T4pos (Lk : List (ℕ × PGraph (Fin 2))) (hLk : ∀ q ∈ Lk, 2 ≤ q.2.g.nW ∧ (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1) (k s : Bool) (a b  …
1963: theorem lwExpTerm3_T4zero {E t : ℝ} (hE : |E| < 2) (ht : t = 0) (k s : Bool) (a b : Zd d (sz.L n)) : ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) * (SB  …
2029: def LwExpG5'OfExpand (d : ℕ) : Prop := LWG5Expand d → LWExpG5' d
2031: theorem lwExpG5'_of_expand (d : ℕ) : LwExpG5'OfExpand d :=
2177: def LwCutExpOfExpand (d : ℕ) : Prop := LWExpI1K d → LWExpI23K d → LWExpI41K d → LWG5Expand d → LWCutExp d
2180: def LwTermEXPOfExpand (d : ℕ) : Prop := LWExpI1K d → LWExpI23K d → LWExpI41K d → LWG5Expand d → LWtermEXP d
2183: theorem lwCutExp_of_expand (d : ℕ) : LwCutExpOfExpand d := fun h1 h23 h41 hx =>
2186: theorem lwTermEXP_of_expand (d : ℕ) : LwTermEXPOfExpand d := fun h1 h23 h41 hx =>
2191: def lwExpTerm3_instGraph : LGraph (Fin 2) (Fin 1) where solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 0) (Sum.inl 1), SEdge.mk false false (Sum.inl 0) (Sum.inl 1), SEdge.mk true true (Sum.inr 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 0) (Sum.inr 0)] waved := [WEdge.mk false true (Sum.inr 0) (Sum.inr 0), WEdge.mk false true (Sum.inr 0) (Sum.inr 0)] dotted := [DEdge.mk false (Sum.inl 0) (Sum.inr 0), DEdge.mk false (Sum.inr 0) (Sum.inl 1), DEdge.mk false (Sum.inl 0) (Sum.inl 1)] coeff := 1
2208: theorem lwExpTerm3_instGraph_nM : lwExpTerm3_instGraph.nM = 1 :=
2210: theorem lwExpTerm3_instGraph_normal : lwExpTerm3_instGraph.Normal :=
2212: theorem lwExpTerm3_instGraph_attached : LWAttached lwExpTerm3_instGraph.pack :=
2216: theorem lwExpTerm3_instGraph_ext : ∀ a b : (lwExpTerm3_instGraph.pack).E', (lwExpTerm3_instGraph.pack).g.molOf (Sum.inl a) = (lwExpTerm3_instGraph.pack).g.molOf (Sum.inl b) → a = b :=
2232: theorem lwExpTerm3_inst_prec1 (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst) : Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
2243: theorem lwExpTerm3_inst_graph_order : lwExpTerm3_instGraph.scalingOrder = 7 :=
2248: theorem lwExpTerm3_inst_bridge (k s : Bool) (a b : Zd 3 (sz0.L 0)) : ((1 / 16 : ℝ) : ℂ) ^ (if k then 1 else 2) * ((((sz0.W 0 : ℕ) : ℂ) ^ 3) * ∑ a₁, ∑ a₂, ∑ a₃, (if k then LWExpKp sz0 0 (STflowE z0 0) (1 / 16) a₁ a₂ else (SB 3 (sz0.L 0) (sz0.lam 0) a₁ a₂ : ℂ)) * (SB 3 (sz0.L 0) (sz0.lam 0) a₂ a₃ : ℂ) * ∫ ω, Lloop sz0 0 (STflowE z0 0) (1 / 16) ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz0.seqP)) = ((((sz0.W 0 : ℕ) : ℂ) ^ 3) ^ 2)⁻¹ * ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl 3 (sz0.L 0) (sz0.W 0) x = a), ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl 3 (sz0.L 0) (sz0.W 0) y = b), ∫ ω, (LWG5Graph k s).val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP) :=
2262: theorem lwExpTerm3_inst_G5 (hx : LWG5Expand 3) (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst) (hDec : STDecay sz0 (STflowE z0) tInst) : Prec sz0 (U := fun n => {_p : (Bool × Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
2279: theorem lwExpTerm3_inst_cut (h1 : LWExpI1K 3) (h23 : LWExpI23K 3) (h41 : LWExpI41K 3) (hx : LWG5Expand 3) (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst) (hDec : STDecay sz0 (STflowE z0) tInst) : Prec sz0 (U := fun n => {_p : (Bool × Bool) × (Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) //
2291: theorem lwExpTerm3_inst_term (h1 : LWExpI1K 3) (h23 : LWExpI23K 3) (h41 : LWExpI41K 3) (hx : LWG5Expand 3) (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst) (hDec : STDecay sz0 (STflowE z0) tInst) : Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
```
Narrative.
* File 2301 lines, imports the five modules of the ticket; no `sorry`, `admit`, `axiom`, `native_decide` (grep on the file: no hits). Helpers carry the stem `lwExpTerm3_`; 17 are `private`.
* Target 2 (`lwExpTerm3_bridge`): `Lloop` (`lwExpTerm2_Lloop5`) and `LGraph.val` (`sum_pi_fin_succ`) become the same fivefold sum (`lwExpTerm3_Lloop5_expand`, `lwExpTerm3_val_expand`); the sums over `(a₁,a₂,a₃)` collapse by `lwExpTerm2_dw_blocks` (`lwExpTerm3_collapse`, `lwExpTerm3_alg`); `S`, `S⁺` by `lwExpTerm2_hS`, `lwExpTerm2_hSp`; integrals and sums commute by `lwExpTerm2_BM_*` (`lwExpTerm3_BM_val`). Powers as pinned: `t^(if k then 1 else 2)`, `(W^d)^(-2)`.
* Target 3 (`lwGraphPrec1`): `lwExpTerm3_det` is `lwGtoAG_holds` with `ξ = min(cc·lwXiVar, Ψ)`; `auxVal` for `q = 0`, `q = 1` (`lwExpTerm3_auxVal_zero/_one`: two molecular edges at the internal molecule from `LWAttached`, AM-GM, `lwXi_ward_sum`, `lwXiVar_symm`). `S, S⁺ = O(t)` is `lwExpTerm3_Sp_decay` (from `S⁺ = S + m² S⁺ S` and `lwSplus_decay`); `Ψ = N^τ' √Bctl` from `STLocalEntry` (`lwExpTerm3_entry_whp`); `(eq:Gbyxi)` from `lwGbyXi_holds` with its premise `lwExpTerm3_hent` (`scaleFacts_R1`, `W^τ ≤ N^(τ/d)`); radii `r = (log W)^(3/2)`, `R = |E'⊕I'| r`, `ρ = 2R + 1` (`lwXiRad_holds`, `lwTail_log32`); `≺ → 𝔼` (`lwExpTerm_prec_integral`) is applied to `X = t^(-n_W)·Γ` (the floor `N^(-K) ≤ R` fails for `t^(n_W) R` when `t n` is small); `t^(n_W) = 0` by `lwExpTerm3_val_zero`; envelope `lwExpTerm3_X_norm_le`.
* Target 4 (`lwExpG5'_of_expand`): `t n = 0`: `lwExpTerm3_Lloop5_zero`, `lwExpTerm3_T4zero` (`‖·‖ ≤ (W^d)⁻³`, `K⁺ = 0`); `t n > 0`: bridge, `LWG5Expand`, `lwGraphPrec1` at `τ/2` for the finite list (`Filter.eventually_all_finite`), `lwExpTerm3_graph_pair_bound` (`t^(n_W) ≤ t^e`, `B^(ord/2) ≤ B^(5/2)`, or `B²` at `x = y`; graphs with `ext 0 = ext 1` vanish at `x ≠ y`), `lwExpTerm3_pairsum`, `W^(-d) ≤ (𝔡⁻²+1) B` (`STBctl_ge`). The index condition `ĝ²/L^d ≤ 1 - t` is carried, not used.
* Target 5: `lwCutExp_of_terms` ∘ target 4, then `lwTermEXP_of_cut` (one-liners).
* Instances: `lwExpTerm3_inst_term`, `_cut` (hypotheses: `LWExpI1K`, `LWExpI23K`, `LWExpI41K` of LW-14d, `LWG5Expand 3` of LW-14e, the five ST local laws), `_G5` (hypotheses: `LWG5Expand 3`, the five ST local laws); `lwExpTerm3_inst_bridge`: `n = 0`, `t = 1/16`, `E = STflowE z0 0`, every `(k, s, a, b)`, no hypothesis; `lwExpTerm3_inst_prec1`: `lwExpTerm3_instGraph` (`n_M = 1` by `decide`, `Normal` and `LWAttached` by `decide`, `lwExpTerm3_instGraph_ext`, `scalingOrder = 7` by `lwExpTerm3_inst_graph_order`), hypotheses `STLocalEntry`, `STLmax` only.
* Registry (Axioms.lean): `LWG5Expand` added to `owedProps` (line 164, after `LWExpG5'`), `LWAttached` to `structuralProps` (line 314); nothing deleted. The final assembly rule (`lwExpG5'_holds`, registry deletions) is not done here (ticket: whichever of T2254/LW-14e merges last).
* Hypotheses the proofs do not use (carried as pinned): `STLmax` in target 3; `LWAvgLaw`, `STLK`, `STDecay` in target 4.
* The preflight's three extra steps (`S⁺ = O(t)`, `hent`, the `t^(-n_W)` rescaling) are inside the file; the Lean changes of target 3 span `lwExpTerm3_det` (line 596) to `lwGraphPrec1`.

## (c) Verified Mathlib names (all used in the file, which builds; one per line)
`List.filter_append_perm`, `Nat.card_eq_one_iff_unique`, `Nat.card_eq_zero`, `Finset.sum_bij`, `Finset.sum_eq_single`, `Finset.sum_comm`, `Finset.sum_filter`,
`Finset.sum_mul_sum`, `Filter.eventually_all_finite`, `Filter.eventually_all`, `List.finite_toSet`, `List.prod_eq_zero`, `List.exists_mem_of_length_pos`,
`Pi.uniqueOfIsEmpty`, `Real.rpow_le_rpow_of_exponent_ge`, `Real.rpow_le_rpow_of_nonpos`, `Real.one_le_rpow_of_pos_of_le_one_of_nonpos`,
`Real.rpow_le_one_of_one_le_of_nonpos`, `Real.sqrt_eq_rpow`, `Real.rpow_intCast`, `Real.mul_rpow`, `Real.inv_rpow`, `zpow_le_zpow_right₀`,
`pow_le_pow_of_le_one`, `one_le_inv₀`, `inv_anti₀`, `inv_mul_cancel₀`, `mul_inv_cancel_left₀`, `pow_eq_zero_iff`, `le_of_sq_le_sq`,
`probReal_univ` (`μ.real univ = 1`), `integral_finsetSum`, `integral_const_mul`, `integral_const`, `Fintype.card_fun`.
Absent or deprecated (tool log): `measureReal_univ_eq_one`, `decide_and`, `pow_eq_zero_iff_of_pos'` (unknown identifiers); `integral_finset_sum`, `if_true`, `if_false`, `dif_pos`, `dif_neg`, `if_neg` (deprecated; replaced by `integral_finsetSum`, `ite_true`, `ite_false`, `dite_true`, `dite_false`).

## (d) Open issues and paper-delta candidates
* Owed by LW-14e: `LWG5Expand` (pin of the check file, registered in `owedProps`); with LW-14d's three pins it gives `LWExpG5'`, `LWCutExp`, `LWtermEXP` (`lwCutExp_of_expand`, `lwTermEXP_of_expand`).
* The file has 2301 lines against the ticket's estimate of 1150-1400 (the preflight's three extra steps and the `q = 1` list bookkeeping).
* T2255a: `B:84` ("each `Γ_μ` with `q ∈ {0,1}`"): the waved edges are `O(t)` and `(Gammamuxy)` carries `t^(n_W)`, which cancels the `t^(1 or 2)` of `(eq;I42inG)` since `n_W ≥ 2`; the merged `lwSplus_decay` has no factor `t`, so `lwExpTerm3_Sp_decay` proves `‖S⁺_xy‖ ≤ t C W^(-d) e^(-c d_B)` in this file. (T2255a, T2255b are the ticket's expected deltas (a), (b); the prover did not re-read `B:74-90`, so what the paper states there is not checked here.)
* T2255b: `B:74`: the `x = y` term needs `W^(-d) ≤ (ĝ²+1) W^(-d) B_{t,0}` (`STBctl_ge`), i.e. `B_{t,0} ≥ c W^(-d)`, not stated.
* T2255c: `B:84-90` uses `ξ` for the attached edges and `Ψ` for the others; the file uses `ξ' = min(N^τ ξ, Ψ)` for all edges (same bound `η⁻¹ Ψ^auxOrd`, no separate `ξ ≺ Ψ`).
* T2255d: `≺ → 𝔼` has a polynomial floor `R ≥ N^(-K)` that fails for `R = t^(n_W) η⁻¹ B^(ord/2)` at small `t`; the proof applies it to `t^(-n_W)Γ` (route, not a statement difference).
