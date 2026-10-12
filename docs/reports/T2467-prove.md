Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 20:35:54 UTC 2026

Binding for this run: Amend 1 (BA side in the new leaf `Chain/Step2EventsGenTw`; `Chain/DecayGenTw` not edited) and UN-C4 (the `T2467.md:39` comparison literal reads as R1,
`∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`). Notation: `N=(WL)^d`, `y=2(n+1)` (so `L=2y, W=y^5, lam=y^-6, N=8y^18` at `sz0`), `Dm`, `D'` as in
`Step2Events.lean:853` (`ST_good_prob`). Band sources: `Step2Events.lean` (E), `Step2Iterate.lean:1049` (`ST_Bdata_holds`), `Defs/Sizes.lean:214` (`Bctl`).

### (i) Exponent table

| # | quantity | constraint (source) | value / slack |
|---|---|---|---|
| 1 | `𝔠,𝔡,κ,ε` | `Admissible 𝔠 𝔡` (F1): `N^𝔠≤W`, `W^{-d/2+𝔡}≤lam≤𝔡⁻¹`, `N→∞` (`Sizes.lean:177`) | `𝔠=1/6, 𝔡=κ=ε=1/10`; `ln N^{1/6}=2.43 ≤ ln W=3.47` at `n=0`; all `n<300` (script) |
| 2 | F2, window | `T0 n<1`, `t n≤T0`, `s≥0`; `T0=lemT z0` | `[s,t]=[0,1/16]≤lemT z0`; `1-lemT=9.05e-6` at `n=0`; `1-t=15/16` |
| 3 | F3 `κm` | `0<κm≤Im m`, `eta=(1-u)Im m>0` (`DecayGen_Spec`, `DecayGen.lean:91`); only `eta>0` is read (E3, E4) | band `κm=√κ/2=0.158 ≤ Im mE(1/2)=0.968`; `eta(1/16)=0.908`. BA `κm=κ` (`DecayGenTw.lean:75`) |
| 4 | `STBdata` (generic) | `cB=(𝔡⁻²+1)⁻¹`, `c=min(2𝔡𝔠,ε)/2`, proof device `N^c≥5` (`Step2Iterate:1049ff`) | `cB=1/101`, `c=1/60`; device holds for `N≥8.7e41` (not used at the instance) |
| 5 | `STBdata` (instance) | `cB W^{-d}≤Bctl(u)≤N^{-c}`, `u∈[0,1/16]`; band instance `hBd_sz0` (`Step2Events.lean:1689`) | `(cB,c)=(1/2,1/4)`, true for all `n<300` (script), also for `(1/101,1/60)` |
| 6 | `ε₀, Ψ` | `ε₀=dc/4≤d/2`; `W^{-d/2}≤Ψ≤W^{-ε₀}` for `Ψ²=(1+cB⁻¹)Bctl`; sufficient `1+cB⁻¹≤W^{dc/2}` (`Step2Events.lean:396-428`) | instance `ε₀=3/16<3/2`; `3≤W^{3/8}`: `3.67` at `W=32` (slack ×1.22). Generic constants need `W≥2.2e80` (`y≥1.2e16`): not used; direct check on true `Bctl` holds all `n<300` |
| 7 | `ε₁, δ₀` (E1) | `N^{ε₁}Bctl^{1/4}≤δ₀` | instance `ε₁=1/8, δ₀=3` (`Bctl≤3W^{-3}, N≤W^6`): margin `×6.4` at `n=0`; generic `ε₁=c/8=1/480, δ₀=1` also holds |
| 8 | `Λ` (E3, E4) | `Λ≥N^{ε₁}` (E3), `Λ≥2N^{ε₁}` (E4), `Λ≥N^{ε₁}` (good event, `hΛ`) | one `Λ=2N^{1/8}` serves all three; slack 0 for (E4) |
| 9 | grid count `C₁` | `(K+1)·#V≤N^{C₁}`; `#(Idx×Idx)=N²`, `#STLab=4L^{2d}`, `#(Fin 2×STLab)=8L^{2d}`; `K=⌈N^{CK}⌉` gives `C₁=CK+5` | `K≡16`: `C₁=5` (E1), `4` (E3), `5` (E4); all `n<300` |
| 10 | `hcardLab` | `#STLab≤N^3` for `N≥4` (`ST_card_lab_le:172`) | `4L^6≤N^3`, all `n<300` |
| 11 | `Dm` (E5) | `D'+1+3≤Dm`: union over `#STLab≤N^3` labels needs `3-Dm≤-(D'+1)`; `2N^{-(D'+1)}≤N^{-D'}` iff `N≥2` | `D'=1`, `Dm=D'+4=5`, **exponent slack 0 (sharp)**; at `n=0` actual ratio `10^{14.75}` |
| 12 | `hρ` | `N^{-Dm}≤ρ₁ STprof²`, `STprof≥N^{-(1+D)}` (`ST_prof_lower_N:1085`) | `D=1, ρ₁=1`: `N^{-5}≤N^{-4}`, exponent slack 1 |
| 13 | (E2) `Di, a₀` | `W^{-Di}≤Bctl(s)^{1/5}STprof`; then `ST_init_cmp:1198` gives LHS `≤ 2N^{ε₁}Bctl^{1/5}STprof` | `Di=6(1+3)=24`, `a₀=2N^{1/8}Bctl(0)^{1/5}`; `W^{-24}≤Bctl^{1/5}N^{-2}` all `n<300` |
| 14 | `hKcap`, `Kf` | `0≤Kf≤(log W)^10·ellT`; `ellT=min(max(lam/√(1-u),1),L)` | `lam/√(1-t)≤1` so `ellT=1`; `Kf≡0` allowed; `gridStep=1/256≥0`, `K≠0` |
| 15 | F7, F9 | no exponent. F7: `C.L n t ![σ₀,σ₁,σ₁] ![a₀,y,a₁]=C.L n t ![σ₁,σ₁,σ₀] ![y,a₁,a₀]` (trace cyclicity of the 3-loop); F9: `∃Hm` with `GMM,LM` at `Hm` equal to `G-M, L`, measurable, and `Cm.Pp{Hpath∈S}=μ{Hm∈S}` | model-free hypothesis predicates; discharged at band (`bandStep2_Grid`) and BA (`baStep2_Grid`), compiled in probe `t/T2454:RBM3D/Probe/T2454Pins.lean` |
| 16 | target 11 | needs F1 (`Admissible`, gives `W→∞` and `ε₀≤d/2`, `STB_eps_le:1320`), F7, `3≤d`; no `Im z`, `lemT`, F2 or F3 (`Step2Events.lean:1355-1455` read) | `d=3`; band proofs 72 + 29 lines |
| 17 | UBA-C1 | no target reads `gK`/`g₀` (`grep -c 'gK\|g₀'` of the check file: 0); BA `lam0=BAflowLam0` is carrier data of `baStep2Mat`, not read by a statement; size-level quantities read `sz.lam` | not triggered; R1 at `gK=sz.lam, A=1` holds (script last line) |

### (ii) One concrete nondegenerate instance (`d=3`)

`sz0` (`Defs/Sizes.lean:260`), `flow_z0` (`z_n=1/2+iN^{-4/5}`, `Induction/Defs.lean:413,435`), `s≡0, t≡T≡1/16`, `K≡16`, `cB=1/2, c=1/4, ε₁=1/8, δ₀=3, D=1, D'=1, Dm=5, Di=24,
Λ=2N^{1/8}, ρ₁=1, Kf≡0`, `mk=bandStep2Mat sz0 (STflowE z0)`, `T0=lemT(z0 n)`; the instance is the band instance of `Step2Events.lean:1870-1920` with the Dm of this ticket. Every `n<300`
is checked at 80 digits (no `N=0`, no empty index set, no collapsed window: `N≥2.1e6`, `1-t=15/16`); the inequalities hold from `n=0`, no astronomically large `n` is needed.
External hypotheses (`STLWTgL`, `STEMn2ExpgL`, `STStep1WeakgL`, `STScaleInvgL`, `STDecaygL`, the (E5) martingale tail, the identity, the remainder, `LWtermG`, `LWtermExpG`) are other gates' outputs and stay hypotheses; the
limit computation for each is the quantity checked here (`Bctl`, `lemT`, `eta`, `ellT`) at the data they quantify over.

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2467/inst.py
Bandwidth N^(1/6)<=W                                                     all n<300: True
WO W^(-3/2+1/10)<=lam<=10                                                all n<300: True
locDomain N^(-9/10)<=Im z<=1, |Re z|=1/2<=2-kap                          all n<300: True
1/16<=lemT z0<1 (F2: T0<1)                                               all n<300: True
Bdata[inst] cB W^-3<=Bctl(0), Bctl(1/16)<=N^-c                           all n<300: True
Psi[inst] W^-3<=Psi^2<=W^(-2 eps0), eps0=dc/4<=d/2                       all n<300: True
Bdata[STBdata] cB W^-3<=Bctl(0), Bctl(1/16)<=N^-c                        all n<300: True
Psi[STBdata] W^-3<=Psi^2<=W^(-2 eps0), eps0=dc/4<=d/2                    all n<300: True
E1 eps1=1/8,delta0=3                                                     all n<300: True
E1 eps1=c/8 (c=1/60),delta0=1                                            all n<300: True
grid E1: (K+1)N^2<=N^5                                                   all n<300: True
hcardLab: 4L^6<=N^3                                                      all n<300: True
grid E3: (K+1)*4L^6<=N^4                                                 all n<300: True
grid E4: (K+1)*8L^6<=N^5                                                 all n<300: True
E5 union: 4L^6 N^-Dm <= N^-(D'+1);  2N^-(D'+1)<=N^-D'                    all n<300: True
hrho: prof>=N^-(1+D), D=1, rho1=1: N^-Dm<=N^-4                           all n<300: True
E2 W^-24<=Bctl(0)^(1/5) N^-2                                             all n<300: True
hKcap: ellT=min(max(lam/sqrt(1-u),1),L)=1 so Kf=0 ok; 0<=0<=(log W)^10   all n<300: True
grid step (t-s)/K = 1/256 >= 0 ; K=16 != 0
n=0: L=4 W=32 N=2.09715e+6 lam=0.01562 lemT-1=-9.051e-6 Bctl(1/16)=3.305e-5 N^-1/4=0.02628
n=9: L=40 W=3200000 N=2.09715e+24 lam=1.562e-8 lemT-1=-3.603e-20 Bctl(1/16)=3.255e-20 N^-1/4=8.31e-7
n=99: L=400 W=320000000000 N=2.09715e+42 lam=1.562e-14 lemT-1=-1.435e-34 Bctl(1/16)=3.255e-35 N^-1/4=2.628e-11
n=0 margins (log10): E5 union slack: log10(N^-2 / (4L^6 N^-5)) = 14.75 ; E1 3/(N^(1/8)Bctl^(1/4)) = 6.4138
F3 band: kappa_m=sqrt(kappa)/2=0.15811 <= Im mE(1/2)=0.96825 ; eta(u=1/16)=(1-u)Im m=0.90773 > 0
UBA-C1 R1 at the comparison pair gK=sz.lam, A=1: 0<=lam^2, lam^2<=lam^2, lam^2<=1*lam^2 (not triggered: no target reads gK)
ALL OK
```

Layout (ticket 1a item (v), Amend 1; closure over `^import RBM3D\.` lines of the worktree `RBM3D-wt/T2467` at `c986735f`):

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2467/closure.py
Step2EventsGen planned imports: Induction.Step2Events, Induction.Step2Core, Chain.Step2Gen, Chain.LWGen, Chain.DecayGen
  closure size 98; BA modules 0; forbidden (Step2Iterate/OptL2*/LWTermHolds/LWExpCert*) []
Step2EventsGenTw planned imports: Chain.Step2EventsGen, BA.LWPinsBA, BA.Step2BA, BA.EMn2BA, BA.FlowPins
  closure size 259 (new file Step2EventsGen contributes the 98-module generic closure); BA modules 27
  Chain/Step2EventsGen*.lean files in worktree: []
  Step2Iterate in closure(Step2EventsGen): False
importers of RBM3D.Chain.DecayGenTw         ['RBM3D.lean']
importers of RBM3D.Chain.Step2EventsGen     []
importers of RBM3D.Chain.Step2EventsGenTw   []
importers of RBM3D.BA.LWPinsBA              ['RBM3D.lean', 'RBM3D/BA/TwistPins.lean', 'RBM3D/Graph/BAAuxGraph2B.lean', 'RBM3D/Graph/BAExp14a.lean', 'RBM3D/Graph/BAExp14aB.lean', 'RBM3D/Graph/BAZetaExp.lean']
importers of RBM3D.Chain.DecayGen           ['RBM3D.lean', 'RBM3D/Chain/DecayGenTw.lean', 'RBM3D/Chain/Step34GenTw.lean']
```

### Verdicts (mathematics only)

- **Target 8 (`STScaleInvgL`, `ST_LW_sectionsg`): PASS.** Rows 1-2, 4-6, 14; the band proof (`Step2Events.lean:348-464`) reads from the flow only `Admissible` (F1) and `T0<1` (F2) (`Bctl>0`, `W→∞`); `eta` enters the conclusion as a symbol.
- **Target 9 (`STEvWeakg, STEvInitg, STEvLWg, STEvMGg` and the four theorems): PASS.** Rows 3, 7-10, 13, 15; (E1), (E2) read no spectral fact, (E3), (E4) read F3 only through `eta>0`.
- **Target 10 (`STGoodAtg`, `ST_good_probg`): PASS.** Rows 8-12; `Dm=D'+4` is sharp, the pinned hypothesis `D'+1+3≤Dm` matches (`T2467-check.lean:345`, `Step2Events.lean:874`).
- **Target 11 (`STBdatagL`, `stLWBgL_of_LWtermG`, `stLWTgL_of_LWtermExpG`): PASS.** Rows 4-5, 16; the bridges need F1, F7 and `3≤d` only.
- **Layout under Amend 1: PASS.** `Step2EventsGen` closure has 0 `BA/` modules and no `Step2Iterate`/`OptL2*`/`LWTermHolds`/`LWExpCert*`; the leaf needs no `Chain.DecayGenTw` import (F3 at BA is inline, `DecayGenTw.lean:75`), so `DecayGenTw` keeps its importer list `['RBM3D.lean']`.
- **UBA-C1 / UN-C4: not triggered** (row 17); no stop rule fires.
- **Finding for the dispatcher (no stop):** the second X1-C1 grep of the ticket (`T2467.md:40`, `withLam|lam0|BAflowLam0|seqHflowBA|gK` on `RBM3D/Chain/Step2EventsGen*.lean`, "is empty") now also matches the new leaf `Step2EventsGenTw.lean`; the pinned BA shapes use `withLam` and `BAflowLam0` (`T2467-check.lean:399,403-406,412`), so the leaf must contain them. The 1b will read that grep on `Step2EventsGen.lean` (and `Step2EventsGenB.lean`) only.
- Ticket items (iii) copy table, (iv) `open private` list, (vi) premise scan are name-level and outside section (a) by the 1a rules.

**Overall: PASS** (targets 8, 9, 10, 11).

### (a′) Preflight corrections — Mon Oct 12 21:11:34 UTC 2026
None. The instances use the (a) data (rows 9-13: `C₁ = 5, 4, 5`, `Dm = D' + 4 = 5`, `Di = 24`, `K ≡ 16`, `(cB, c) = (1/2, 1/4)`, `(ε₁, δ₀) = (1/8, 3)`); the delivered imports are those of the layout row.

## (b) Script output (worktree `RBM3D-wt/T2467`, branch `t/T2467`; scratch scripts in the session scratchpad, not committed)
```
$ lake build RBM3D.Chain.Step2EventsGen RBM3D.Chain.Step2EventsGenTw 2>&1 | tail -1
Build completed successfully (3999 jobs).
$ lake build 2>&1 | tail -2        # full library: #assert_rbm_axioms and the premise scan
non-vacuity certificates: 0 of 111 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4306 jobs).
$ wc -l RBM3D/Chain/Step2EventsGen.lean RBM3D/Chain/Step2EventsGenTw.lean   # stop line 2,000 per file; reserve B only above 1,800; 1a-audit estimate 1,101 = 1,038 + 58 + 5
    1351 RBM3D/Chain/Step2EventsGen.lean
     171 RBM3D/Chain/Step2EventsGenTw.lean
$ git diff main...t/T2467 --stat      # main = 8ea70675, merge-base c986735f; output condensed to one line
 RBM3D.lean | 2 +;  RBM3D/Chain/Step2EventsGen.lean | 1351 +;  RBM3D/Chain/Step2EventsGenTw.lean | 171 +;  RBM3D/Test/Axioms.lean | 6 +;  4 files changed, 1530 insertions(+)
$ git diff main...t/T2467 -- RBM3D/Induction/ RBM3D/BA/ RBM3D/Chain/{Step2Gen,DecayGen,LWGen,Carrier,DecayGenTw}.lean | wc -l   ->   0   # brace list is shorthand for the five paths
# layout / closure (closure2.py, from the files on the branch)
RBM3D.Chain.Step2EventsGen     direct imports: ['Induction.Step2Events', 'Induction.Step2Core', 'Chain.Step2Gen', 'Chain.LWGen', 'Chain.DecayGen']
   closure size 98; BA modules 0; forbidden (Step2Iterate/OptL2*/LWTermHolds/LWExpCert*): []; Step2Iterate in closure: False
RBM3D.Chain.Step2EventsGenTw   direct imports: ['Chain.Step2EventsGen', 'BA.LWPinsBA', 'BA.Step2BA', 'BA.EMn2BA', 'BA.FlowPins']
   closure size 260; BA modules 27; forbidden modules in the closure: LWExpCert*, LWTermHolds, Step2Iterate (allowed for the leaf only); Step2Iterate in closure: True
importers of RBM3D.Chain.Step2EventsGen     ['RBM3D.lean', 'RBM3D/Chain/Step2EventsGenTw.lean']
importers of RBM3D.Chain.Step2EventsGenTw   ['RBM3D.lean']
importers of RBM3D.Chain.DecayGenTw         ['RBM3D.lean']
$ grep -n '^import RBM3D.BA' RBM3D/Chain/Step2EventsGen.lean   ->  (no output)   # Amend 1 item 6: read on Step2EventsGen.lean, not on the leaf
# statement diff against T2467_* (stmtdiff.py: normalised text; Audit.lean = the check file + 25 examples, uncommitted)
theorems ST_LW_sectionsg, ST_event_{weak,init,lw,mg}g, ST_good_probg, stLWBgL_of_LWtermG, stLWTgL_of_LWtermExpG: text equal 8 of 8;  definitions STScaleInvgL, STBdatagL, STEv{Weak,Init,LW,MG}g, Step2EventsGen_{Grid,Rot3,Flow}: equal 9 of 9
STGoodAtg fields in order: ['weak', 'init', 'lw', 'mg', 'mart', 'rem', 'ident']
seven field types occur, in order, in the pin T2467_GoodAtFields text: True
$ lake env lean Audit.lean   -> exit 0   # `example : T2467_X := @X` x8, `Iff.rfl` x9, STGoodAtg field by field, ST_good_probg -> T2467_ST_good_probg through STGoodAtg, BA/band shapes
$ lake env lean Ax.lean      # #print axioms of the 60 new public declarations (49 theorems, 10 defs, 1 structure): 60 lines `[propext, Classical.choice, Quot.sound]`, 0 other; e.g.
ST_LW_sectionsg, ST_event_weakg, ST_event_initg, ST_event_lwg, ST_event_mgg, STGoodAtg, ST_good_probg, stLWBgL_of_LWtermG, stLWTgL_of_LWtermExpG: [propext, Classical.choice, Quot.sound]  (each its own line)
# compiled nonempty instances (Gen = Chain/Step2EventsGen.lean, Tw = Chain/Step2EventsGenTw.lean line numbers)
ST_LW_sectionsg Gen:1185; ST_event_weakg Gen:1195, Tw:132; ST_event_initg Gen:1202; ST_event_lwg Gen:1216, Tw:94
ST_event_mgg Gen:1230, Tw:113; ST_good_probg Gen:1246; stLWBgL_of_LWtermG Gen:1292, Tw:144, Tw:158; stLWTgL_of_LWtermExpG Gen:1297, Tw:148, Tw:164
```
Left as hypotheses (other gates' pins): `bandPin STLWTgL 3`, `bandPin STEMn2ExpgL 3` (band examples), `BASTLWT d` (BA examples; `baSTEMn2Exp` is merged and applied), `STStep1WeakgL`, `STDecaygL`, `STScaleInvgL`, the `Bctl` and scale-cap bounds at BA, (E1)-(E4), the tail (E5), the identity and the remainder (target-10 example), `LWtermG 3`, `LWtermExpG 3` (band target-11 examples; closed in the leaf).
Discharged: F1-F2, F3, F7, F9, `hd`, `hDm` at `Dm = 5` (equality), the cardinalities, size, `hΔ`, `hΛ`, `hρ`, `hcardLab`, `hBd`, `hKcap`, `hsmall` at `sz0`, `z0`, `[0, 1/16]`, `K ≡ 16`.

### Copy table (iii): band decl, file (E = Step2Events, C = Step2Core), line -> new name (stem `Step2EventsGen_` dropped) : line in `Step2EventsGen.lean`
```
Prec sz -> PrecL sz μ, PrecPT sz -> PrecPTL sz μ:  ST_prec_mono_eventually E:49->prec_mono_eventually:116;  ST_prec_of_le_ev E:59->prec_of_le_ev:126;  ST_prec_sup E:76->prec_sup:142
    STB_prec_dom (private) E:1261->prec_dom:156;  ST_PT_of_sections C:500->PT_of_sections:173;  ST_sections_of_PT C:515->sections_of_PT:187
pathP, pathH, seqHflow, ST_pathP_eq_seqP -> Cm.Pp, Cm.Hpath, Hm, F9 law clause:  ST_whp_grid C:422->whp_grid:201;  ST_grid_whp_of_sections E:93->grid_whp_of_sections:245
    ST_grid_whp_zero E:118->grid_whp_zero:273;  ST_model_le_path E:566->model_le_path:304
(mE E).im, √κ/2 -> (C.m n).im, κm (F3);  STJhatM -> STJhatMg;  STLM rotation -> loopFine / F7:  ST_cstar_le E:1188->cstar_le:324;  ST_JhatM_nonneg E:699->JhatMg_nonneg:598
    STB_loop_rot (private) E:1283->loopFine_rot3:99;  STB_EGt_eq_LWE (private) E:1294->EGt_eq_LWE:979
targets (STFlow, lemT, STflowE -> F1-F2, mk.toFlowFM; (mE E).im (1-u) -> Cm.eta; band functionals -> g-forms; STB_prec_dom -> prec_dom; F1, F3, F7, F9):
    STScaleInv E:159->STScaleInvgL:438;  ST_LW_sections E:348->ST_LW_sectionsg:448;  ST_event_weak E:609->ST_event_weakg:608
    ST_event_init E:786->ST_event_initg:641;  ST_event_lw E:637->ST_event_lwg:675;  ST_event_mg E:710->ST_event_mgg:738
    STGoodAt C:963->STGoodAtg:813;  ST_good_prob E:853->ST_good_probg:834;  STBdata E:209->STBdatagL:966
    STLWB_of_LWterm E:1355->stLWBgL_of_LWtermG:1005;  STLWT_of_LWtermExp E:1427->stLWTgL_of_LWtermExpG:1080
measurability and model readings `Step2EventsGen_ST{LM,LKM,GMM,JhatM,EGtM,EEkM,EEM}g_measurable`, `_ST{EGtM,EEkM,JhatM,LKM}g_eq`: Step2Defs.lean:167-225, under F9 clauses 1-4.  `ST_flow_im_pos`, `ST_mE_im_ge`: projections of `DecayGen_Spec`, not copied.
open private (Step2Events): STB_trace_six (F7 proof), STB_eps_le (bridge); instances only: hBd_sz0 hKcap_sz0 hsmall_sz0 hcard_idx hcard_lab hcard_fin2lab hW_sz0 size_ge_17 sI_nonneg sI_le KI KI_ne VI cardVI_le measF
```

### Registry (`Test/Axioms.lean`, `owedProps`: 5 lines and 1 comment line) and the premise scan
```
scan before the lines (full lake build, RBM3D.lean:538): 5 premise(s) that no theorem of this development proves are in none of the ledgers:
  [RBM.BA.STDecaygL, RBM.BA.STGoodAtg, RBM.BA.LWtermG, RBM.BA.STScaleInvgL, RBM.BA.LWtermExpG]      after the lines: no unregistered premise (build above)
owners: STScaleInvgL T1 / T1-BA;  STDecaygL main induction (band) / BA-V;  LWtermG, LWtermExpG BA-L6 (band proved: band_LWtermG, band_LWtermExpG);  STGoodAtg T1's P4
```
`STGoodAtg` is reported although no public theorem here has it as a hypothesis: its seven field projections are theorems that take it as a binder (a scratch script over the scan's `binderConsts` lists `STGoodAtg.{mg,rem,init,lw,weak,mart,ident}`), as for the registered `STGoodAt`. `STLWTgL`, `STEMn2ExpgL`, the event sets and `Step2EventsGen_{Flow,Rot3,Grid,Law}` are concluded by theorems; `STStep1WeakgL` is registered.

### Greps
```
$ spectral X1-C1 grep on Step2EventsGen.lean: 80 hit lines = 12 docstring, 2 band bridge (bandFM_*: lines 443, 975), 9 band fact/reading (Step2EventsGen_band*), 57 instance (section Instances), 0 in a generic statement or proof
$ same on the leaf: 25 hit lines = 7 docstring, 4 BA carrier facts (baLaw, baGrid: `seqP (sz.withLam 0)`, `seqHflowBA`), 10 examples at the BA family, 4 closed band instance of target 11
$ grep -nE 'withLam|lam0|BAflowLam0|seqHflowBA|gK' RBM3D/Chain/Step2EventsGen.lean   ->  (no output);  grep -c on the leaf: 29 (BA carrier shapes of `T2467-check.lean:399-412`)
$ grep -cE 'gK|g₀' on both files  ->  0 and 0   # UBA-C1 / UN-C4 not triggered;   grep 'sorry\|admit\|native_decide\|^axiom' on both files  ->  (no output)
name clash: `git grep -lw` of the 60 new public names on main (8ea70675): no hit; pinned names and the stem `Step2EventsGen` on the other 73 branches `t/T24*`: no hit outside `Probe/`
```

### Narrative (b)
- Layout (Amend 1): `Chain/Step2EventsGen.lean` (1,351 lines) has targets 8-11, F1-F2, F7, F9, the generic helpers, the band readings and the band instances; its imports are `Step2Events`, `Step2Core`, `Step2Gen`, `LWGen`, `DecayGen` (closure 98 modules, 0 `BA/`, no `Step2Iterate`).
  The BA side is the new leaf `Chain/Step2EventsGenTw.lean` (171 lines); `Chain/DecayGenTw.lean` is not edited (diff empty). `Step2EventsGenB` is not used (1,351 < 1,800).
- Every target proof is the band proof with the model objects replaced (copy table): `sz.Prec -> PrecL sz μ`; `pathP/pathH/seqHflow -> Cm.Pp/Cm.Hpath/Hm` through the F9 law clause; `(mE E).im (1 - u) -> Cm.eta`; `STB_loop_rot -> F7`.
  `eta > 0` in (E3), (E4) reads F3 and `T0 < 1`; `ST_LW_sectionsg` reads `Admissible` (`W → ∞`) and `T0 < 1` (`Bctl > 0`). No generic statement reads `‖m‖ = 1`, a scalar `m`, `mE`, `gK` or `g₀` (greps).
- Statements: the 8 theorem statements and 9 definitions are the check-file text with `T2467_X` read as `X`; `STGoodAtg` is a structure whose seven fields are the seven conjuncts of `T2467_GoodAtFields`, in order. `Step2EventsGen_bandGoodAt` is a proved reading of the band `STGoodAt` (`ring` for `eta = (mE E).im * (1 - u)`, `bandStep2_STgDrift` for the identity).
- Additions to the ticket text: `Step2EventsGen_Law` (the last conjunct of F9, the hypothesis of the transfer helpers) with `Step2EventsGen_bandLaw`, `Step2EventsGenTw_baLaw`, which conclude it so the scan does not report it; `Step2EventsGen_cstar_le`; band examples of the helpers; BA examples of (E1), (E3), (E4) and target 11; `Step2EventsGenTw_band_STLWBgL`, `_band_STLWTgL` (target 11 closed at the band by `band_LWtermG`, `band_LWtermExpG`).
- The registry has 5 lines; `STGoodAtg` is one of them through its projections, unlike the ticket's expectation. The ticket's second X1-C1 grep and its BA-import grep use the glob `Step2EventsGen*.lean`, which includes the leaf; they are read on `Step2EventsGen.lean`, as the preflight predicted.
- `STBdatagL` is a definition with its band bridge (`Iff.rfl`); its BA proof is T1-BA's (ticket). Targets 8 and 9 have no closed band instance (they need the pins `STLWTgL`, `STEMn2ExpgL`, Step 1, `STDecaygL`, `STScaleInvgL`). Target 11 sits in `Step2EventsGen` (bridges 76 and 35 lines with docstrings, under the 150-line rule), its closed band forms and BA forms in the leaf.
- `Dm = D' + 4 = 5` is used at equality in the target-10 example. No port from RBM1D/RBM2D: all copied text is from `Induction/Step2Events.lean`, `Step2Core.lean`, `Step2Defs.lean` of this tree.

## (c) Verified Mathlib names (`#check` scratch on the branch, exit 0 except the one absent name)
`Finset.measurable_sup'`, `Finset.measurable_sum`, `Measurable.of_eval_matrix`, `measurable_pi_apply`, `Measurable.pow_const`, `Measurable.div_const`, `Measurable.norm`, `measurableSet_lt`, `Finset.lt_sup'_iff`, `Finset.le_sup'`,
`Set.mem_ofPred_eq` (the build warns `Set.mem_setOf_eq` is deprecated in its favour), `inv_anti₀`, `pow_le_pow_left₀`, `pow_le_pow_iff_left₀`, `le_inv_mul_iff₀`, `Real.rpow_le_rpow_of_exponent_le`, `Real.sq_sqrt`, `tendsto_rpow_atTop`, `Nat.floor_le_floor`, `MeasureTheory.measure_mono`.
Absent at top level: `measure_iUnion_fintype_le` (it is `MeasureTheory.`-qualified; not used directly).

## (d) Open issues and paper-delta candidates
- `T2454a`: F7 (`Step2EventsGen_Rot3`, trace cyclicity of the 3-loop) is an explicit premise of `stLWBgL_of_LWtermG`, `stLWTgL_of_LWtermExpG`; proved for a fine matrix (`Step2EventsGen_loopFine_rot3`), hence at the band and at BA.
- `T2454b`: F9 (`Step2EventsGen_Grid`: the model matrix and the law `(5.1)` of the grid state) is an explicit premise of (E1)-(E4); proved at the band (`Step2EventsGen_bandGrid`) and at BA (`Step2EventsGenTw_baGrid`). No other Lean/paper statement difference.
- Pins of other gates stay hypotheses of the examples (list above); none is proved or `sorry`ed here. `STScaleInvgL`, `STDecaygL`, `LWtermG`, `LWtermExpG`, `STGoodAtg` are in `owedProps`.
- Size: 1,522 lines in the two files against the 1a-audit estimate 1,101 (full pinned statement texts, the helper and BA examples); both under the stop line 2,000.
