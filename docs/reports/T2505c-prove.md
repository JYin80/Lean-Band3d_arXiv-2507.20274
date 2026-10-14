Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 12:51:13 UTC 2026

Row c (U3s4c), targets 10-15, branch `t/T2505c` at b610fbdb (rows a, b merged). Band sources (read only): `Induction/QtNonzeroFlow.lean`, `QtNonzeroFlowLift.lean`, `QtNonzeroBoot.lean` §5-§6; generic inputs: row a `Chain/QtBootGen`, `QtXiRoundLiftGen`, row b `Chain/QtNonzeroGen`, `QtNonzeroEndGen`. Scripts (Python, no Lean): `<scratchpad>/T2505c/rowc.py`, `rowc2.py`; scratchpad = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad`.

### (i) Exponent table
Chain: `stOeqNZPTgL''_of` (11) = per-section `nzFlow_core` (`QtNonzeroFlow:577`) at `nzGridEndNg` with `ε₀ = τ/2`, `D₁ = D+2`, `k = n_`, `τR = ε/2` (`v3_premises_of_stFlow`), union of 4 events of mass `N^{-(D+2)}`; lift (12) = envelope + one-sided net, mesh `δ ≤ N^{-(6n_+18+2c)}`, `c` = the pinned FlowMod exponent (band `c=1`, i.e. `6n_+20`, `QtNonzeroFlowLift:450`); round (13) = `newPQ` at `A=∅`; bootstrap (14) = row a `stXiBootRgL'_of_round`. Instance values: `n_=3, τ=1, D=1, 𝔠=1/6, ε=𝔡=κ=1/10`. "grid" = `rowc.py` first line.
| item | value (instance) | constraint | slack: instance / grid minimum |
|---|---|---|---|
| `e0 = min(τ/2,1)`, `ε₁ = e0/8` | 1/2, 1/16 (`QtNonzeroEndGen:433,441`) | H1 `ε₁<e0`; H2, H3 `2ε₁<e0` | 7/16, 3/8, 3/8 / 0.04375, 0.0375, 0.0375 |
| `D''=2(k+2)/𝔠+1`, `D'=D''+1`, `τ'=1` | 61, 62, 1 (`:436,441`) | H4 `ε₁+k-𝔠D''/2<e0` | 121/48 / 2.0488 |
| `D_Y=D_t=k+2`, `cA=2^k` | 5, 8 | H5, H6 `k-D_Y<e0` | 5/2 / 2.05 |
| `D₁=D+2`; grid-walk net `C_K = D₁+2(Cmax+2k+2)+D''+16k+40` | 3; 168+2Cmax (`:439`) | hC1-hC6 (`:448-453`) | 117, 131, 567/4, 772/5, 3341/20, 96 / 54, 63.18, 74.15, 84.13, 94.105, 77.1 |
| projected initial event (`nzFlow_initQ`, `QtNonzeroFlow:497`) | `2^{n_} ≤ N^{ε₁/2}`, `ε₁/2 = 1/32` | `ε₁/2>0` (`STLKgL` at `ε₁/2`) | 1/32 / 0.003125 |
| union and terminal step | `4N^{-(D+2)} ≤ N^{-D}`; `N^{τ/2} ≤ N^{τ}` | `N ≥ 2`; `N ≥ 1` | `N = 4096` at `n=0` |
| D1 constant `C5 = Ci^k` (row b, merged) | `Ci = 30.1` for `Λg = 𝔡⁻¹ = 10`, `A=1`; `C5 = 2.727e4` | `∃C5` after `(k,κ,𝔡)`, before `(sz,z)`; `Ci ≥ sup` of the one-index kernel | rowc2: 30.024 (L=48) ≤ 30.1; at the instance `L=4,g=1`: 2.019 |
| D1 A-form window / R1 | `(1-u)L² ≤ A·gK²`, `u∈[s,t]`; `lam² ≤ Aof·gK²` | band `A=1, gK=lam`; BA `Aof=(κ+1)/κ` | band: equality at `u=s` (=1), 1/2 vs 1 at `u=t`; BA: `Aof·t0 ≥ 1 ⟺ Im m ≥ κ Im z` (`BAdom`: `κ ≤ Im m, Im z ≤ 1`), slack 0 at `Im m=κ, Im z=1` |
| net mesh of the lift `A_net = 6n_+18+2c` | 38 (`c=1`) | `2^{n_}N^{n_}(3n_N^{2n_+6+c}√δ+N^{2n_+2}δ) ≤ 1` for `δ=N^{-A_net}`, `N ≥ 2^{n_}(3n_+1)` (=80) | LHS 1.05e-9 at `N=4096`; max 1.09e-3 at the smallest admissible `N`, `n_ ≤ 10, c ≤ 10` |
| label count (`nzLift_card_V`, `QtNonzeroFlowLift:629`) | `#V = 7,340,032` (`#(σ,A)=28 ≤ 4^{n_}`, `(L^d)^{n_}=64^3`) | `#V ≤ N^{2n_}`, `N ≥ 4` | `4096^6 = 4.7e21` |
| range | `(1-t)⁻¹ = 32 ≤ N`; `RangeCond(ε/2)`: `N^{-19/20} ≤ 1/32` | `N^{-1+τR} ≤ 1-t` | 3.70e-4 vs 1/32 at `n=0` |
| bootstrap `c = min(2𝔡𝔠, τR)/12`; `C₀=2n_+1` | 1/360; 7; rounds `⌈C₀/c⌉+1 = 2521` | `B_u^{1/6} ≤ N^{-c}`, `u ≤ t` (`qtBoot_contraction`, `QtNonzeroBoot:246`) | real data: 0.5331 ≤ 0.9772 (`n=0`); lemma threshold `N ≥ 2^{2/c₁}`, `c₁=1/30` |
| lower terms (13): `(2Nη_u)⁻¹ ≤ (2κm)⁻¹B_u`, `η=(1-u)Im m` (`DecayGen_Spec`) | `κm = 0.9` | `κm ≤ Im m = 0.968`, `u<1` | 8.07e-3 ≤ 2.37e-2 (`n=0`, `u=t`) |
Eventual thresholds (conclusion side, as in merged `inst_OeqNZPT''`, `QtNonzeroFlow:882`): initQ `N ≥ 2^96 = 7.9e28`; H1-H6 `N > 1.5e22` (τ=1), `1.1e46` (τ=1/2); contraction lemma `N ≥ 2^60`; they do not enter the hypotheses.
Quantifier order (structural): `𝔠_d` after `(κ,ε,𝔡,C_d)`; D1 `C5` after `(k,κ,𝔡)`; FlowMod `c` after `(κ,ε,𝔡)`; all before `(sz,z)`. No `∀ n` drift premise.

### (ii) One nondegenerate instance (`d=3`, `szB`: `L=4`, `W_n=n+4`, `lam≡1`, `N_n=(4(n+4))³`; `z_n=1/2+i/64`, merged `flow_zB` `Step34Pins:785`; `s≡15/16`, `t≡31/32`; `n_=3, p=1`; band carrier `Aof=1, gK=lam`)
`cd <scratchpad>/T2505c && python3 -I rowc.py`
```
GRID n_{2,3,4,6} tau{.1,.5,1,3} D{.1,1,10} c{.01,1/6,.5,1} eps{.01,.1,.5,1} Cmax{0,1,50}; min slack (all > 0):
   hC1=54  hC2=63.18  hC3=74.15  hC4=84.13  hC5=94.105  hC6=77.1  H1=0.04375  H2=0.0375  H3=0.0375  H4=2.0488  H5=2.05  H6=2.05  initQ eps1/2=0.003125
LIFT arithmetic at the smallest admissible N = 2^n_(3n_+1), n_<=10, c<=10: max LHS = 0.001093 (<= 1 required); at N=4096,n_=3,c=1: 1.05e-09
msc(z=1/2+i/64) = -0.247983+0.960467i ; lemT = 0.983992 >= t=31/32 = 0.968750 : True ; |lemE| = 0.5000 <= |Re z| = 1/2 : True
band energy |E|<=1/2: Im mE(E) >= sqrt(15)/4 = 0.9682 ; kappa_m = 0.90 <= Im m: True (DecayGen_Spec)
flow data kappa=eps=dd=1/10 c=1/6 s=15/16 t=31/32 n_=3 p=1 | StochDom tau=1, D=1 | tauR=eps/2=1/20 | bootstrap c=min(2*dd*c,tauR)/12 = 0.002778 = 1/360 : True ; C0=2n_+1=7 ; rounds ceil(C0/c)+1 = 2521
  n= 0 W= 4 N=   4096 | W>=N^(1/6) True | W^(-3/2+dd)<=lam=1<=1/dd=10 True | N^(-1+eps)=5.61e-04<=Im z=1/64 True | RangeCond N^(-1+eps/2)=3.70e-04<=1-t=1/32 True | B_t=2.296e-02 N^-c=0.9772 B^(1/6)=0.5331<=N^-c True | (N eta)^-1=8.07e-03 <= (Im m)^-1 B_t=2.37e-02 True
  n=16 W=20 N= 512000 | W>=N^(1/6) True | W^(-3/2+dd)<=lam=1<=1/dd=10 True | N^(-1+eps)=7.27e-06<=Im z=1/64 True | RangeCond N^(-1+eps/2)=3.77e-06<=1-t=1/32 True | B_t=1.837e-04 N^-c=0.9641 B^(1/6)=0.2384<=N^-c True | (N eta)^-1=6.45e-05 <= (Im m)^-1 B_t=1.90e-04 True
  n=40 W=44 N=5451776 | W>=N^(1/6) True | W^(-3/2+dd)<=lam=1<=1/dd=10 True | N^(-1+eps)=8.65e-07<=Im z=1/64 True | RangeCond N^(-1+eps/2)=3.98e-07<=1-t=1/32 True | B_t=1.725e-05 N^-c=0.9578 B^(1/6)=0.1607<=N^-c True | (N eta)^-1=6.06e-06 <= (Im m)^-1 B_t=1.78e-05 True
regime: (ii) 1-s = 1/16 <= lam^2/L^2 = 1/16 (equality, boundary) ; 0<=s<t<1, s<t non-collapsed: True ; collapsed section u=s is in TimeIcc: True
R1 band: lam^2 = 1 <= Aof gK^2 = 1 : True ; guard 0<gK<=lam: True ; D1 window (1-u)L^2 <= A gK^2 at u=s, mid, t: [True, True, True]
R1 BA (BAt0 = Im m/(Im m+Im z) MFixedPoint:279; BAflowLam0 = sqrt(t0) lam FlowPins:386; BAdom: kappa<=Im m, Im z<=1): Aof=(kappa+1)/kappa, Aof*t0 >= 1 and gK<=lam on grid: True (min slack 0)
label set: #{(sigma,A)} = 28 <= 4^n_ = 64 ; #V = 7340032 <= N^(2n_) = 4096^6 = 4722366482869645213696 : True
instance exponents (tau=1,D=1,n_=3,c=1/6,tauR=1/20): e0=1/2 eps1=1/16 D1=D+2=3 D''=61 D'=62 tau'=1 C_K=168+2Cmax ; slacks {'hC1': '117', 'hC2': '131', 'hC3': '567/4', 'hC4': '772/5', 'hC5': '3341/20', 'hC6': '96', 'H1': '7/16', 'H2': '3/8', 'H3': '3/8', 'H4': '121/48', 'H5': '5/2', 'H6': '5/2', 'initQ eps1/2': '1/32'}
eventual thresholds (conclusion side only, N > threshold): initQ 2^n_ <= N^(eps1/2): N >= 2^(2n_/eps1) = 2^96 = 7.92e+28 ; union 4N^-(D+2) <= N^-D: N>=2 ; mesh N >= 2^n_(3n_+1) = 80 ; (1-t)^-1=32 <= N ; contraction 2 <= N^(c1/2), c1 = min(2 dd c, tauR) = 1/30: N >= 2^60 = 1.15e+18
```
`python3 -I rowc2.py` (D1 constant at the instance and the H1-H6 thresholds; kernel of `QtNonzero:299`, `Defs/Block.lean:36-44`; budget formulas of `QtNonzero:891-905`):
```
A=1 g=1 T1: L=4: 2.019  L=8: 2.094
A=1 g=10 T1: L=4: 5.468  L=12: 29.546  L=24: 29.916
A=1 g=10 T1 at L=48 (w=1-1e-9): 30.024 ; Ci := 30.1 > this (saturation in L)
tau=1 (eps0=tau/2, e0=0.5): H1-H6 hold for all N > e^51.06 = 1.49e+22 (C5=2.727e+04, Lambda_g=10); szB index with N_n=(4(n+4))^3 above it: n >= 6158432
tau=0.5 (eps0=tau/2, e0=0.25): H1-H6 hold for all N > e^106.02 = 1.11e+46 (C5=2.727e+04, Lambda_g=10); szB index with N_n=(4(n+4))^3 above it: n >= 556859084286368
```
Every hypothesis holds at every `n` (printed at `n = 0, 16, 40`): admissibility (`W ≥ N^{1/6}`, `(eq:WO)` at `𝔡=1/10`), `locDomain`, `t ≤ lemT = 0.983992`, `RangeCond`, `STCaseII` (equality, `s<t`: non-collapsed; the collapsed section `u=s` lies in `TimeIcc`), D1 window, R1, `DecayGen_Spec`. No `N = 0`, empty index, collapsed window or `False` premise; thresholds above are conclusion-side only (the example unfolds `∀ᶠ` by `Eventually.exists`, as `QtNonzeroFlowInst`). Left as hypotheses of the example, as in the merged `inst_OeqNZPT''`: the pins of other gates (`STLKgL s`, `STStep2ConclgL`, the pair hypotheses `Ξ̂ ≺ 1`), D1 and `KLipFam`/`FlowModFam` (merged classes, band discharges in rows a, b). The ticket names no external input for targets 10-15; the concrete limit computed is the D1 saturation in `L` (30.024 at `L=48`, rowc2) and the thresholds above.

### Verdicts
- Target 10 (D3 pins, `T2505_NZConclPTgL''`, `T2505_OeqNZPTgL''`, `T2505_NZConclgL''`, `T2505_OeqNZgL''`): PASS. Props only; index set nonempty (`σ=(+,-,+), A={0,1}`; `#V` above); texts equal the band pins with `PrecPTL`/`PrecL`.
- Target 11 (`stOeqNZPTgL''_of`): PASS. Constants close with positive slack (table); `hR1` (`lam² ≤ Aof·gK²`, as `hcmp` of `st6_ini_nonzerog`, `Step6KitGen:401`) is a guarded per-index premise of `nzGridEndNg` (row b) that the ticket's family table does not list as its own row (UBA-C1 names it): 1b lists it. Not a binding-text or stop-rule change.
- Target 12 (`stOeqNZgL''_of`): PASS. Mesh arithmetic with the factor `2^{n_}` closes for every `c ≥ 0` (table), `M = 2^{n_}(3n_+1)` in `LemDecCalELip_envg`.
- Target 13 (`stXiRoundNZgL_of`): PASS. Lower terms need only `κm ≤ Im m`, `η=(1-u)Im m`, `ZeroModeGen_WardCls`.
- Target 14 (`stOeqQtNZgL'_of`): PASS. `c`, `C₀` as row a; no new exponent.
- Target 15 (band re-derivations, instances, registry): PASS. Registry lines exist on this branch: `Test/Axioms.lean:121` ("no generic proof"), `:214` ("proofs: U3s3, U3s4"); line `:217` (row a) ends "case (ii): T2505 row c" (not in the binding row-c text; observation for 1b).
No binding text and no stop rule moves: 1a-audit not needed.

## (b) Script output (written Wed Oct 14 13:24:22 UTC 2026; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2505c`, branch `t/T2505c`)
Commits: 0d2b65e4 T2505c: Chain/QtNonzeroBootGen (targets 13-15), imports, registry lines;6f09d473 T2505c: Chain/QtNonzeroFlowGen (targets 10-12, band re-derivations, instances);

### B1 builds, check
$ lake build RBM3D.Chain.QtNonzeroFlowGen RBM3D.Chain.QtNonzeroBootGen 2>&1 | tail -1
Build completed successfully (3953 jobs).
$ lake build > fullbuild.txt   [run finished Wed Oct 14 13:13:23 UTC 2026; file in the scratchpad]
$ grep -n 'axiom audit:\|^registry:' fullbuild.txt | cut -c1-175; tail -2 fullbuild.txt
7141:info: RBM3D.lean:630:0: axiom audit: 15299 theorems, 4724 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
7272:registry: 2 borrowed + 122 owed + 140 structural + 7 refuted + 19 superseded; 151 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4400 jobs).
exit 0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2505-check.lean > check_out.txt; echo exit $?; grep -c ' error' check_out.txt
exit 0
0

### B2 wc -l per file against both census figures (ticket: x1.24 / x1.06)
$ python3 -I ev_all.py   (section 1)
QtNonzeroFlowGen.lean: 1145 lines; band re-derivation section 97; instance section 108; rest 940; census 866 / 919
QtNonzeroBootGen.lean: 780 lines; band re-derivation section 101; instance section 86; rest 593; census 419 / 444
row c total 1925 lines; census 1285 / 1365 (cap 1950); ticket stop size 2000 per new file

### B3 imports, importers, cone, layering, diff
$ grep -nE 'sorry|admit|^axiom |native_decide|import RBM3D\.BA|Chain\.Step2Kern' RBM3D/Chain/QtNonzero{Flow,Boot}Gen.lean | wc -l
       0
$ grep '^import' RBM3D/Chain/QtNonzeroFlowGen.lean | sed 's/import RBM3D\.//'
Chain.QtNonzeroEndGen Chain.QtXiRoundLiftGen Chain.GridGoodGen Chain.NQLinGen Chain.B45Gen Chain.NQEndFlowGen Induction.QtNonzeroFlow Induction.QtNonzeroFlowLift Induction.LemDecCalELip 
$ grep '^import' RBM3D/Chain/QtNonzeroBootGen.lean | sed 's/import RBM3D\.//'
Chain.QtNonzeroFlowGen Chain.QtBootGen Chain.ZeroModeGen Chain.Step6KitGen Induction.QtNonzeroBoot 
$ grep -rn 'import RBM3D.Chain.QtNonzero\(Flow\|Boot\)Gen' RBM3D RBM3D.lean
RBM3D/Chain/QtNonzeroBootGen.lean:6:import RBM3D.Chain.QtNonzeroFlowGen
RBM3D.lean:626:import RBM3D.Chain.QtNonzeroFlowGen
RBM3D.lean:627:import RBM3D.Chain.QtNonzeroBootGen
cone (script: transitive `import RBM3D.*`): QtNonzeroFlowGen 247 modules / 244,619 lines; QtNonzeroBootGen 248 modules / 245,400 lines (band sources Flow+FlowLift+Boot: 209 / 199,748)
$ git diff b610fbdb..HEAD --name-only; git diff b610fbdb..HEAD --stat -- RBM3D/Induction RBM3D/BA RBM3D/Graph | wc -l
RBM3D.lean RBM3D/Chain/QtNonzeroBootGen.lean RBM3D/Chain/QtNonzeroFlowGen.lean RBM3D/Test/Axioms.lean 
       0
$ grep -n 'RBM1D\|RBM2D' RBM3D/Chain/QtNonzero{Flow,Boot}Gen.lean | wc -l   (ports from RBM1D/RBM2D: none)
       0

### B4 `#print axioms` of the 28 new public declarations (script: public names -> axioms_all.lean, grouped by axiom set)
$ lake env lean axioms_all.lean  (28 `#print axioms` lines, grouped)
28 declarations: [propext, Classical.choice, Quot.sound]
  STNZConclPTgL'', STOeqNZPTgL'', STNZConclgL'', STOeqNZgL'', bandFM_STNZConclPT'', bandFM_STNZConcl'', bandFM_STOeqNZPT'', bandFM_STOeqNZ'', stOeqNZPTgL''_of, stOeqNZgL''_of,
  QtNonzeroFlowGenCheck.stOeqNZPTgL''_band, QtNonzeroFlowGenCheck.stOeqNZgL''_band, QtNonzeroFlowGenCheck.stOeqNZPTgL''_band3, QtNonzeroFlowGenCheck.stOeqNZgL''_band3,
  stOeqNZPT''_holds_of_gen, stOeqNZ''_holds_of_gen, QtNonzeroFlowGenCheck.inst_OeqNZPTgL'', QtNonzeroFlowGenCheck.inst_OeqNZgL'', stXiRoundNZgL_of, stOeqQtNZgL'_of,
  QtNonzeroBootGenCheck.stXiRoundNZgL_band, QtNonzeroBootGenCheck.stOeqQtNZgL'_band, QtNonzeroBootGenCheck.stOeqQtNZgL'_band3, QtNonzeroBootGenCheck.stXiRoundNZgL_band3,
  QtNonzeroBootGenCheck.stXiRoundNZ_holds_of_gen, stOeqQtNZ'_holds_of_gen, QtNonzeroBootGenCheck.inst_XiRoundNZgL, QtNonzeroBootGenCheck.inst_OeqQtNZgL'

### B5 target statements, extracted by script (`python3 -I ev_stmt.py`; premise binders and conclusions; the four D3 texts diffed against the check)
== statement diff against the check texts T2505_* (names mapped; docstrings stripped) ==
STNZConclPTgL''  [QtNonzeroFlowGen.lean:72]  vs T2505_NZConclPTgL'' [check:98]:  identical=True
STOeqNZPTgL''  [QtNonzeroFlowGen.lean:88]  vs T2505_OeqNZPTgL'' [check:114]:  identical=True
STNZConclgL''  [QtNonzeroFlowGen.lean:94]  vs T2505_NZConclgL'' [check:120]:  identical=True
STOeqNZgL''  [QtNonzeroFlowGen.lean:110]  vs T2505_OeqNZgL'' [check:136]:  identical=True
QtNonzeroFlowGen.lean:523  theorem stOeqNZPTgL''_of
   premises (32): d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU hB45 hKerFam hR1 hT0
   conclusion: STOeqNZPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0
QtNonzeroFlowGen.lean:846  theorem stOeqNZgL''_of
   premises (34): d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU hB45 hKerFam hR1 hT0 hKLip hFM
   conclusion: STOeqNZgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0
QtNonzeroBootGen.lean:433  theorem stXiRoundNZgL_of
   premises (34): d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU hB45 hKerFam hR1 hT0 hKLip hFM
   conclusion: STIngRgL d STCaseII law Flow (fun sz z => (mkM sz z).toFlowFM) T0 (fun sz z s t => STXiRoundgL' (mkM sz z).toFlowFM (law sz) s t)
QtNonzeroBootGen.lean:507  theorem stOeqQtNZgL'_of
   premises (34): d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU hB45 hKerFam hR1 hT0 hKLip hFM
   conclusion: STOeqQtNZgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0
$ lake env lean rowc_check.lean   (check Part-2 texts + `example : @STNZConclPTgL'' = @T2505_NZConclPTgL'' := rfl`, same for the other three, and the conclusions of 11, 12 read as `T2505_OeqNZPTgL''`, `T2505_OeqNZgL''`; a mismatched control `STNZConclPTgL'' = T2505_OeqNZgL''` errors)
exit 0
output bytes:        0

### B6 compiled nonempty instances (script: `example` / `theorem inst_*` in the two instance sections; all compile in B1)
QtNonzeroFlowGen.lean lines 1034-1141: 1043:inst inst_OeqNZPTgL''; 1055:inst inst_OeqNZgL''; 1068:ex; 1073:ex; 1080:ex; 1090:ex; 1101:ex; 1112:ex; 1119:ex; 1123:ex; 1128:ex; 1133:ex; 1136:ex
QtNonzeroBootGen.lean lines 691-776: 699:inst inst_XiRoundNZgL; 711:inst inst_OeqQtNZgL'; 724:ex; 735:ex; 742:ex; 753:ex; 758:ex; 764:ex; 769:ex
Reading (all at `d = 3`, band carrier `bandStep2Mat szB`, `szB`: L = 4, W = n+4, N = (4(n+4))^3, `zB`: z_n = 1/2 + i/64, s = 15/16 < t = 31/32, C_d = 1; `STLKgL s`, `STStep2ConclgL` stay hypotheses):
  t11 `inst_OeqNZPTgL''` (1043): `stOeqNZPTgL''_of` with every row discharged (`stOeqNZPTgL''_band3`) applied at the data: `STNZConclPTgL''`; t12 `inst_OeqNZgL''` (1055): `STNZConclgL''`.
  t13 `inst_XiRoundNZgL` (699): `STXiRoundgL'`; t14 `inst_OeqQtNZgL'` (711): `STXiBootgL'` (the merged text `STOeqQtNZgL'`); both from the band family, `𝔠_d ∈ (0, 1/100]` produced.
  t10: the index set of the pins is nonempty (1119, 1123: `σ = sig3`, `A = {0, 1} ⊇ I_diff σ`); bridges at d = 3 (1133, 1136). t15: merged-pin corollaries through `inst_ing` (1068, 1073; 753, 758) and `bandFM_STOeqQtNZ'` (764).
  Private lemmas at the data: `QtNZFlowGen_initQ` (1080, at one size index 1090), `_collapsed` (1101), `_meas_proj` (1112), mesh arithmetic with N = 4096, n_ = 3, c = 1 (1128); `QtNZBootGen_round_of_NZ` (724, from `inst_OeqNZgL''`), `_inv_Neta` (735), `_term_le` (742), `_prec_sum` (769).

### B7 hypothesis-rule greps (scripts `ev_rules.py`; ticket regexes C1, X1-C1, X1-C4, U5S-C3, TN-C4)
X1-C1 regex over the 12 new public statements outside the band/instance sections (`KLloopOf` excepted, as the ticket): 0 hits in the 8 generic statements (the 4 D3 texts, `stOeqNZPTgL''_of`, `stOeqNZgL''_of`, `stXiRoundNZgL_of`, `stOeqQtNZgL'_of`);
  hits only in the 4 band bridge statements `bandFM_STNZConclPT''`, `_STNZConcl''`, `_STOeqNZPT''`, `_STOeqNZ''` (`seqP`, `STFlow`, `STflowE`, `lemT`: band re-derivation, labelled); outside the band/instance sections of the proofs: hits only in those bridges and `KLloopOf` (hKK).
X1-C4 `(def|abbrev|structure) <pinned name>` in the two files: QtNonzeroFlowGen [] QtNonzeroBootGen []  (the private bundle `QtNZFlowGen_Facts` is not on the list)
TN-C4 `STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds`: QtNonzeroFlowGen [] QtNonzeroBootGen []
U5S-C3 `∀ (sz : Sizes d)` hits in QtNonzeroFlowGen: 52 (premise binders: E lam Flow Hf T0 hC hEK hExp hKK hKL hKT hKcal hL hLaw hR1 hRow hS hSeq hSpec hT0 hU hW hWard hm Ψ)
U5S-C3 `∀ (sz : Sizes d)` hits in QtNonzeroBootGen: 48 (premise binders: E lam Flow Hf T0 hC hEK hExp hKK hKL hKT hKcal hL hLaw hR1 hRow hS hSeq hSpec hT0 hU hW hWard hm Ψ)
  each hit is a family row of B9 (rows 1-6, 3-4-7-11, 12, R1); no premise is `∀ n` drift/hierarchy; guarded ones carry `0 < κ → Flow sz κ ε 𝔠 𝔡 z →`; unguarded `hLaw hC hWard hSeq hS hKK` are carrier facts for every `(sz, z)` (the merged texts of T2491/T2498 rows 1-13), `hSE` is the pin `STSEforLngL`.

### B8 name-clash grep of the 28 new public short names (script: `grep -rnE` in `RBM3D/` and `RBM3D.lean`, the two new files excluded)
new public short names: 28; hits outside the new files: 1, `RBM3D/Test/Axioms.lean:214` (the registry comment written by this ticket, `stOeqQtNZgL'_of`); `grep -rn` of the same names in `docs/tickets/` not run (ticket's sibling scan 2026-10-14: 0 hits).

### B9 family-premise table as used (the 34 premises of `stOeqNZgL''_of`, `stXiRoundNZgL_of`, `stOeqQtNZgL'_of`; `stOeqNZPTgL''_of` has the first 32, no `hKLip`, `hFM`)
| ticket row | Lean binder | guard | pinned `∃` | read by |
|---|---|---|---|---|
| 1-6 (T2498 `:62-78`) | `hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK` | `0 < κ → Flow …` on `hSpec hL hW hKcal hEK`; `hLaw hC hWard` per `(sz, z)` | `𝔠d` (of the pin) | t11-t14 via `gridGoodNgL_of`, `nqLinGoodgL_of` |
| 3, 4, 7, 11 | `hm hSeq hS hRow hKK hExp hKL hKT hU` | `hm hRow hExp hKL hKT hU` guarded; drift classes `∀ᶠ n` | — | t11-t14 via `nzGridEndNg` |
| 9 | `hB45 : B45Gen_Facts` | inside: `∀ κ > 0, ∃ C₆, ∀ sz ε 𝔠 𝔡 z, Flow … →` | `C₆` after `κ` | `ZeroModeGen_KerSums` t11-t14; `ZeroModeGen_WardCls` t13, t14; other fields unread |
| 12 | `hT0` | `0 < κ → 0 < ε → Flow` | `τ` inside | `RangeCond` t11-t14 |
| 14 (D1) | `hKerFam : QtNZGen_KerNZFam` | inside: `3 ≤ d`, `k ≥ 2`, `Flow`, `∀ᶠ n` | `C5` after `(k, κ, 𝔡)`, before `(sz, z)` | t11-t14 |
| R1 (UBA-C1) | `hR1 : … ∀ n, sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2` | `0 < κ → Flow` | `Aof : ℝ → ℝ` a parameter | t11-t14 (`nzGridEndNg`) |
| 15 / 16 | `hKLip : NQEndFlowGen_KLipFam`, `hFM : QtBootGen_FlowModFam` | inside (merged) | `c` after `(κ, ε, 𝔡)` | t12-t14 (`QtNZLiftGen_lift`, `QtBootGen_Hyp`) |
Not premises: D1 of the alternating endpoint (`QProxyG_KerEK4Fam`), `hTh`, `NQGoodGen_KerNALFam`, any `∀ n` drift or hierarchy statement.

### B10 UBA-C1 as used
R1 (`lam² ≤ Aof κ · gK²`) enters once, as `hR1` into `nzGridEndNg` (t11; row b turns it with `STCaseII` into the D1 window `(1 - u) L² ≤ Aof κ gK²`); t10-t14 carry `STCaseII` as their regime, no `sz.withLam`, no comparison other than R1, no coupling other than `gK`.
Band: `Aof = 1`, `gK = sz.lam` (`(one_mul _).ge`); BA: `Aof κ = (κ + 1) / κ` (preflight (a): `Aof · t0 ≥ 1 ⟺ Im m ≥ κ Im z`, slack 0 at `Im m = κ, Im z = 1`). The guard (g) `0 < gK n → 0 < lam n ∧ gK n ≤ lam n` of the ticket table is read by no proof here.

### B11 registry lines and scan (script: `git diff --word-diff=porcelain -U0 b610fbdb..HEAD -- RBM3D/Test/Axioms.lean RBM3D.lean`, `+`/`-`/`@@` lines)
@@ -625,0 +626,2 @@ import RBM3D.Chain.QtNonzeroEndGen
+import RBM3D.Chain.QtNonzeroFlowGen
+import RBM3D.Chain.QtNonzeroBootGen
@@ -121 +121 @@ def owedProps : List Name :=
-no generic proof
+generic: `STXiRoundgL'` (T2505, `Chain/QtBootGen`)
@@ -214 +214 @@ def owedProps : List Name :=
-it (proofs: U3s3, U3s4);
+it: `stOeqQtgL'_of` (T2505a, `Chain/QtXiRoundLiftGen`, from U3s3's `stOeqQtRoundPTgL''_of`) and `stOeqQtNZgL'_of` (T2505c, `Chain/QtNonzeroBootGen`);
Scan: the full `lake build` (B1, `import RBM3D` + `#assert_rbm_axioms`) accepts the tree; row c adds no `owedProps` line (none of the four new D3 `Prop` defs is a binder of a public theorem; `STXiRoundgL'` is row a's line `:217`).

### B12 G1 note
No band file is edited: B3 `git diff b610fbdb..HEAD --stat -- RBM3D/Induction RBM3D/BA RBM3D/Graph` is empty, so the six band files, `Step3`, `Step4` and every merged `RBM3D/Chain` file are unchanged; the only other files touched are `RBM3D.lean` (two import lines) and `RBM3D/Test/Axioms.lean` (two registry texts).

### B13 Narrative (facts from the files and the logs above)
- Row c on `t/T2505c` from b610fbdb (rows a, b merged, imported, not edited): `Chain/QtNonzeroFlowGen` (t10-t12), `Chain/QtNonzeroBootGen` (t13-t15), two import lines, two registry texts.
- Each generic proof is the band proof with the carrier objects read through `Cm : Step2Mat sz`, a law `μ`, the flow matrix `Hf` and the facts of one flow: `QtNZFlowGen_core`/`_section` are `nzFlow_core`/`nzFlow_section`
  with row b's `nzGridEndNg` for `nzGridEndN`, `gridGoodNgL_of`/`nqLinGoodgL_of` for the good events, `STLKgL` for `STLK`; `QtNZLiftGen_lift` is `nzLift_lift` with `lemDecCalELipG_loops` (`𝓛`, exponent `c`) and
  `NQEndFlowGen_KLip` (`𝒦`); `QtNZBootGen_round_of_NZ` is `qtBoot_round_of_NZ` with `zeroModeCalc_LK_expansion_emptyg` under `ZeroModeGen_WardCls`; target 14 is `stXiBootRgL'_of_round d STCaseII` (row a) after target 13.
- Model-free privates are reused by `open private` (43 names: 31 in `QtNonzeroFlowGen`, 12 in `QtNonzeroBootGen`; list at the top of each file); 15 new private declarations carry the stems `QtNZFlowGen_`, `QtNZLiftGen_`, `QtNZBootGen_`
  (`QtNZFlowGen_Facts` is a private `Prop` bundle, in no public statement, as `NQEndFlowGen_Facts`).
- Generic part (B7): no `|E| < 2`, `‖m‖ = 1` or entry-level band fact; the spectral input is `DecayGen_Spec` (`κm ≤ Im m`, `η_t = (1 - t) Im m`), so `(2Nη_v)⁻¹ ≤ κm⁻¹ B_v` follows from `QtBootGen_inv_one_sub_le`; `LoopForm` and `‖m‖ ≤ 1` are premises.
- Premises: B9. `hR1` is its own guarded row, as (a) said (verdict t11); `hB45` is read for two fields; D1 is row b's `QtNZGen_KerNZFam`. Pinned `∃`: `𝔠d`, `C5`, `C₆`, `c`, all before `(sz, z)`; no `∀ n` premise.
- Differences from the band proofs to check: (i) the mesh is `δ ≤ N^{-(6n_+18+2c)}` with the pinned `c` and `2^{n_}(3n_+1) ≤ N` (`QtNZLiftGen_arith`; band: `c = 1`, `6n_+20`); (ii) the lower-term constant is `κm⁻¹` (band: `(√(κ/2))⁻¹`);
  (iii) the events `Sterm`, `Sinit` are sets of fine matrices through `STLKMg`/`Cm.LM` at `Hf`, transferred by `Step2EventsGen_Law` and `GridGoodGen_LM_eq_L`; (iv) `𝔠_d = min 𝔠G 𝔠L` (no `1/(2d)`, as the band case (ii)).
- Instances: B6; every deterministic hypothesis is discharged by the band discharges (`stOeqNZPTgL''_band` etc., no open hypothesis) and the data of `szB`; `STLKgL s`, `STStep2ConclgL` stay hypotheses of the examples (other gates' pins, as in the merged band instances).
- Calibration (B2): 1,145 and 780 lines against 866 / 919 and 419 / 444; row 1,925 against 1,285 / 1,365, under the cap 1,950 and each file under 2,000. Blocks the census does not count: the four public premise blocks
  (statement lines 55 + 57 + 58 + 57 = 227), the band re-derivation sections (97 + 101 = 198) and the instance sections (108 + 86 = 194); without them 1,306 lines. `lake build` warnings in the two files: 20 long-line warnings, all in the module docstring (lines 13-33).

## (c) Verified Mathlib / core names used (script: every dotted or underscore token of the two files, resolved by `resolveGlobalName` in `lake env lean names.lean`; all resolve; none searched for and found absent)
Complex.norm_I Complex.norm_intCast Complex.norm_natCast Complex.norm_real Complex.norm_two ENNReal.ofReal ENNReal.ofReal_le_ofReal Filter.Eventually.of_forall Finset.Subset.refl
Finset.card_le_univ Finset.exists_mem_eq_sup' Finset.induction_on Finset.le_sup' Finset.le_sup'_of_le Finset.mem_insert_of_mem Finset.mem_insert_self Finset.single_le_sum Finset.subset_univ
Finset.sum_div Finset.sum_insert Finset.sum_le_sum Finset.sum_nonneg Finset.sup'_le LinearMap.continuous_of_finiteDimensional LinearMap.proj Measurable.of_eval MeasurableSet.iUnion
Real.norm_of_nonneg Real.one_le_rpow Real.rpow_add Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.rpow_natCast Real.rpow_neg Real.rpow_nonneg Real.rpow_pos_of_pos Real.sqrt_le_sqrt
Real.sqrt_sq Set.mem_compl_iff Set.mem_ofPred_eq Set.mem_preimage Set.mem_union div_le_div_of_nonneg_left div_le_div_of_nonneg_right div_le_iff₀ div_le_one inv_anti₀ le_self_pow₀ lt_div_iff₀
measurableSet_lt measurable_const MeasureTheory.measure_mono MeasureTheory.measure_ne_top norm_le_pi_norm MeasureTheory.ofReal_measureReal one_le_pow₀ pi_norm_le_iff_of_nonneg
pow_le_pow_left₀ pow_le_pow_right₀ tendsto_rpow_atTop

## (d) Open issues and paper-delta candidates
- `T2505c` (candidate): the lift's mesh `δ ≤ N^{-(6n_+18+2c)}` with the factor `2^{n_}` of `(normQA2)` (`3_5:1466`) and the pinned flow exponent `c` (band `T2299b`: `c = 1`, `6n_+20`); the paper's net remark `3_5:1931` states no exponent.
- `T2505d` (candidate): the generic constants `𝔠_d = min 𝔠G 𝔠L` (no `1/(2d)`), `∃ C5` (D1, row b) and `∃ c` (row 16) pinned before `(sz, z)`; band `T2292a/c/d`, `T2299a` unchanged in kind.
- `T2505e` (candidate): the lower terms of `(eq:expandQAempty)` carry `κm⁻¹` with `κm ≤ Im m` (band `T2304b`: `(√(κ/2))⁻¹`, `κm = √κ/2` at the band), `k_α = 1` included, no averaged law.
- Observation 1: registry line `:217` (row a's `STXiRoundgL'`) still ends "case (ii): T2505 row c"; it is not in the binding row-c text and is left for the dispatcher: case (ii) is `stXiRoundNZgL_of` (T2505c, `Chain/QtNonzeroBootGen`).
- Observation 2: the ticket lists `Step6KitGen` for `QtNonzeroBootGen`; the file compiles without that import (scratch copy, exit 0) and `QtBootGen` imports it, so the import is kept but not read. `hB45` carries unread fields (`DecayGen_WardPair`, `Im m ≤ 1`, the `Θ`-kernel bounds).
- Observation 3: BA discharges (D1 at `Aof κ = (κ+1)/κ`, rows 15, 16, `B45Gen_Facts`) are U3-BA / T2501, not here; no obstruction found, no pinned text changed, no hypothesis added, no stop rule hit.
