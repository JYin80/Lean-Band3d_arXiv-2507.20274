Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 22:22:48 UTC 2026

Sources: `docs/tickets/T2475.md`, `docs/tickets/checks/T2475-check.lean` (`T2475_*`), probe `921369b:RBM3D/Probe/T2449Pins.lean`, `RandomLayerA/B.lean`, `SizesComp.lean`, `BA/*` on main ae791953 (= worktree HEAD; the ticket's input files (`RandomLayerA/B`, `OUInterfaceK`, `PinsK`, `SizesComp`, `BA/UNPins, MReg, MFixedPoint, FlowPins`, `Chain/Carrier`) and toolchain/manifest are unchanged since the ticket's base 8ea70675 (`git diff --stat 8ea70675 main -- <those>` printed nothing)). Mathematics only, no Lean written.

### (i) Exponent table  (`κ'` BA = `(πκ)^5/2048`; sequence: `N=(WL)^d`, `η_LL=N^{-1+2τU}`, `η_Q=ouEtaQ`, `t ≤ ouTStar=N^{-1+τU}`)
| quantity | value | constraint it must satisfy (where from) | slack |
|---|---|---|---|
| `κ'` = `c` (BA, `Flow′`/`Dom′`) | `(πκ)^5/2048` | `κ' ≤ Im m(E+iη)` for `ρ_N(E) ≥ κ`, `0<η≤1` (`BAm_im_lower_window` at `x=E`, `MReg.lean:227`); nonempty bulk needs `πκ ≤ 1` (`MReg` proof, `hk1`) | S0: `Im m0=0.889306` vs `κ'=2.716e-4` (ratio 3.3e3), `πκ_*=0.8893<1` |
| `κ'` = `κ`, `c`, `cT` (band) | `κ`; `c_κ=√(κ(4-κ))/8`; `1/16` | `RandomLayerB_flow_band :351` (`κ>2`: `c=1`, bulk empty) | `cT` unchanged, so band thresholds below are 1 |
| `cT` (BA) | `κ'/(κ'+1)` | `cT ≤ fT=b/(b+a)`, `b=Im m ≥ κ'`, `a=Im z ≤ 1` (b/(b+a) increasing in b, decreasing in a); `1-fT=a/(b+a) ≤ a/κ'`, so `c=κ'`; `fT<1` since `a,b>0` | S0 n=0: `fT=0.99999889` vs `cT=2.715e-4` |
| `Dom′` margin `κ''(κ)` | band `κ`; BA `(πκ)^5/2048` | `0<κ''`; feeds T5 `MLout` (needs `0<κ''`, `0<ε`, `0<𝔡`) | exact |
| `ε` in `Dom′`, LL scale | `2τU` | window `N^{-1+ε} ≤ η_LL=N^{-1+2τU} ≤ 1`; `η_LL ≤ 1` as `-1+2τU<0`, `N ≥ 1` (`τU ≤ 1/100`) | equality at the lower end (as merged) |
| `ε` in `Dom′`, Q scale | `min(𝔠(𝔡-𝔡/3),1)=min(2𝔠𝔡/3,1)`; `(1/6,1/10)`: `1/90` | `N^{-1+ε} ≤ η'_Q ≤ 1` for all `n` (`η'` = `η_Q` except finitely many `n`; merged `queDomain`) | `0<ε`, `ε ≤ 2𝔠𝔡/3`; checked at n=0,1,10 below |
| `τU` | `≤ ouTauMax=min(𝔠/12,𝔠𝔡/12,1/100)`; `(1/6,1/10)`: `1/720=0.0013889` | `ouTauMax_slack`: `12τU ≤ 𝔠`, `12τU ≤ 𝔠𝔡`, `τU<𝔠𝔡`, `3τU/2<2𝔠𝔡/3`; `τU<1/2` for `RandomLayerB_LL` | `𝔠/12=1/72` (10×), `1/100` (7.2×) above `1/720` |
| `τD′` LL (`Prod′` argument) | `τU/4` | rows: `t ≤ N^{-τD′}√cT·η` and `(N√cT·η)⁻¹ ≤ N^{-τD′}`; from merged `rowsLL` (`t ≤ N^{-τU/2}η/4`, `4(Nη)⁻¹ ≤ N^{-τU/2}`): both follow iff `N^{τU/2-τD′}=N^{τU/4} ≥ 1/(4√cT)` (the `√fT ≥ √cT` step) | band `4√cT=1`: no condition; BA S0: `1/(4√cT)=15.17` |
| `τD′` Q | `τU/2` | same with `rowsQ` (`t ≤ N^{-τU}η/4`): `N^{τU-τD′}=N^{τU/2} ≥ 1/(4√cT)` | as above (the design's "`N^{τD′} ≥ …`" is the same number) |
| rows 3, 4 of `Prod′` | `L^d(1-t1) ≤ lam², ≤ 1` | `1-t1 ≤ η/c+t` (`1-fT ≤ η/c`, `ζ(t)·fT ≤ t`); merged `rowsLL/rowsQ` take any `c>0`, here `c=κ'` | no new condition |
| direct (unreused) LL condition | `N^{3τU/4} ≥ 1/√cT` | exact requirement for `t ≤ N^{-τU/4}√cT·η_LL` | reused route needs `N^{τU/4} ≥ 15.17` (stronger, so it implies it) |
| eventual thresholds, S0, `τU=1/720` | `log10 N ≥ 3401.4` (LL), `1700.7` (Q); `r1` alone `866.97` | all conditions are `∀ᶠ n`; no hypothesis restricts `n` to a finite window; the first `n` is astronomical (S0: `N=2^21·(n+1)^15`) | see (ii): not a witness, an eventual statement |

Logic of D1/D2 (no table row): `pad_subseq`: if `¬∀ᶠ n, S n → Q n` then `{n | S n ∧ ¬Q n}` is infinite, its `Nat.nth` enumeration `φ` is strictly monotone with `S(φ j)` for all `j`, and the hypothesis gives `∀ᶠ j, Q(φ j)`: contradiction. Applied with `S n := bulk sz κ (E n) n`, `Q n := LLAt K sz τU n (E n) (t n) δ p` (resp. `QueAt`) and the one-sequence lemma at `sz.comp φ` (`E∘φ`, `t∘φ`; `comp_size` gives `ouTStar (sz.comp φ) τU j = ouTStar sz τU (φ j)` by `rfl`; `comp_admissible` needs `Tendsto φ atTop atTop`, true for `StrictMono`). The compatibility then returns `bulk`, `LLAt`, `QueAt` from `sz.comp φ` to `sz` at `φ j`. Hypotheses `Flow′`, `Dom′`, `Prod′`, LL, `Que′`, T5 are `∀ sz`, so they apply at `sz.comp φ` unchanged.

### (ii) One concrete nondegenerate instance, d = 3, `(𝔠,𝔡)=(1/6,1/10)`
Band, `sz0` (`Defs/Sizes.lean:260`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`), `κ=1/10`, `E ∈ {0, 1.8}`, `τU=ouTauMax`:
`python3 .../scratchpad/T2475/band2.py`
```
tauU=ouTauMax=0.0013889 eps=0.011111 4*sqrt(cT)=1.0
n=0 N=2097152 eta_LL=4.965e-7 eta_Q=1.202e-6 lemT(0+i eta_LL)=0.999999503488 | eta_Q in [N^(-1+eps),1]: True | W>=N^(1/6): True | W^(-7/5)<=lam<=10: True | Lemma2.8 facts at E in{0,1.8}: True
n=1 N=549755813888 eta_LL=1.961e-12 eta_Q=1.155e-11 lemT(0+i eta_LL)=0.999999999998 | eta_Q in [N^(-1+eps),1]: True | W>=N^(1/6): True | W^(-7/5)<=lam<=10: True | Lemma2.8 facts at E in{0,1.8}: True
n=10 N=11659991713824860234842112 eta_LL=1.007e-25 eta_Q=5.287e-24 lemT(0+i eta_LL)=1.0 | eta_Q in [N^(-1+eps),1]: True | W>=N^(1/6): True | W^(-7/5)<=lam<=10: True | Lemma2.8 facts at E in{0,1.8}: True
eventual thresholds at tauU=1/720: r1 N^(tauU/2)>=4 <=> log10 N >= 866.966 ; cT-threshold N^(tauU/4)>=1/(4 sqrt cT)=1 holds for every N>=1
```
(`Lemma2.8 facts`: `1/16 ≤ |msc|² < 1` and `1-|msc|² ≤ η/c_κ`, for `η ∈ {η_LL, η_Q}`.) BA, `S0 = clsS 4 (g=3/10)` (`BA/UNPins.lean:884`; `(L,g0)` from the flow point of `MFixedPoint.lean:876-890`: `w=6i/5`, `m_S=L^{-3}tr(gΨ-w)⁻¹`, `t0=Im m_S/Im w`, `g0=√t0·g`, `E_*=0`, `m0=m_S/√t0`; spectrum of `Ψ^{(B)}` on `Z_4^3` = `2(cos+cos+cos)(πk/2)`, `Adj` = `ℓ¹` distance 1, `Defs/Lattice.lean:108`): `python3 .../T2475/ba2.py`
```
flow pt: t0=0.549212073 g0=0.222326531 E_*=6.46e-83 Im m0=0.889306125 resid(self_m at E_*,g0)=1.06e-81
kappa_*=0.28307493 kappa_0=(pi kappa_*)^5/2048=0.00027159794 cT=0.00027152419 1/(4sqrt cT)=15.171752 pi*kappa_*<=1: True
n=0 N=2097152 eta=N^(-19/20)=9.873e-7 fT=0.999998889803 | eta_Q=1.71e-5 fT=0.999980775351 | all of {cT<=fT<1, 1-fT<=eta/kappa_0, Ed kappa_0} ok: True | eta in [N^(-19/20),1], eta_Q in [N^(-1+eps),1]: True True | W>=N^(1/6): True | W^(-7/5)<=g0: True
n=1 N=68719476736 eta=N^(-19/20)=5.067e-11 fT=0.999999999943 | eta_Q=8.414e-8 fT=0.999999905384 | all of {cT<=fT<1, 1-fT<=eta/kappa_0, Ed kappa_0} ok: True | eta in [N^(-19/20),1], eta_Q in [N^(-1+eps),1]: True True | W>=N^(1/6): True | W^(-7/5)<=g0: True
n=10 N=8760324352986371325952 eta=N^(-19/20)=1.428e-21 fT=1.0 | eta_Q=1.774e-13 fT=1.0 | all of {cT<=fT<1, 1-fT<=eta/kappa_0, Ed kappa_0} ok: True | eta in [N^(-19/20),1], eta_Q in [N^(-1+eps),1]: True True | W>=N^(1/6): True | W^(-7/5)<=g0: True
tauU=1/720=ouTauMax: LL needs N^(tauU/4)>=15.1718 => log10 N >= 3401.38 ; Q needs N^(tauU/2)>=15.1718 => log10 N >= 1700.69 ; (band cT=1/16: both =1)
tauU=1/1000 (probe): LL needs N^(tauU/4)>=15.1718 => log10 N >= 4724.14 ; Q needs N^(tauU/2)>=15.1718 => log10 N >= 2362.07 ; (band cT=1/16: both =1)
```
(`Ed κ_0`: `m_E=m/√fT` solves `(self_m)` at coupling `√fT·g0`, energy `BAflowE`, `Im m_E ≥ κ_0`, residual `<1e-40`; this is the `BAReal` datum of `BAEd`.) External hypothesis `UNMLOutBA 3` (V3, `BA/UNPins.lean:110`): the antecedent of the probe instance (`sz0`, `zSeq n=zS(L_n,lam_n)`, `BA/FlowPins.lean:1181`; `κ=1/2, ε=1/10`): `python3 .../T2475/v3.py`
```
n=0 N=2.097e+06 Im m_S=0.832488 Im z_S=0.367512 t0=0.693740 | 1/2<=Im m: True | N^(-9/10)<=Im z<=1: True | t0>=2/3: True
n=1 N=5.498e+11 Im m_S=0.833333 Im z_S=0.366667 t0=0.694444 | 1/2<=Im m: True | N^(-9/10)<=Im z<=1: True | t0>=2/3: True
n=10 N=1.166e+25 Im m_S=0.833333 Im z_S=0.366667 t0=0.694444 | 1/2<=Im m: True | N^(-9/10)<=Im z<=1: True | t0>=2/3: True
limit lam_n->0: m_S -> 1/(-w) = i/1.2, Im m_S -> 0.833333, t0 -> 0.694444 = 25/36 = 0.694444 >= 2/3
```
Sequence limits at S0: `N_n=2^21(n+1)^15 → ∞`; `W ≥ N^{1/6}` iff `W ≥ 4` (`N^{1/6}=(4W)^{1/2}`), true from `n=0` (`W=32`); `(eq:WO)` lower `W^{-7/5}=(2(n+1))^{-7} ≤ g0=0.2223` from `n=0`; upper `g0 ≤ 10`. Closure, importers, name clashes (`S=.../scratchpad/T2475`):
`python3 $S/closure.py /Users/junyin/Lean_proof/RBM3D-wt/T2475; python3 $S/closure2.py; bash $S/clash.sh`
```
generic file closure: 138 modules, BA/* modules: 0 []
importers (transitive) of RBM3D.Universality.GUEPhase.RandomLayerB : 4 ; roots among them: ['RBM3D', 'RBM3D.Main.BUniv', 'RBM3D.Main.BUnivHolds', 'RBM3D.Main.BandTerminal']
importers (transitive) of RBM3D.Induction.SizesComp : 6 ; roots among them: ['RBM3D', 'RBM3D.Main.BandTerminal']
importers (transitive) of RBM3D.BA.UNPins : 5 ; roots among them: ['RBM3D', 'RBM3D.Main.BandTerminal']
direct importers of RandomLayerB: ['RBM3D', 'RBM3D.Main.BUniv']
new modules RandomLayerBG, RandomLayerBGBA exist on main: False
closure(RandomLayerB)=137; + SizesComp = 138 (extra: ['RBM3D.Induction.SizesComp']); BA/* in generic closure: 0
leaf closure = 156 modules; main-branch BA/* modules in it: 8
refs scanned:       19
RBG_Flow=0 RBG_Dom=0 RBG_Prod=0 RBG_Que=0 RBG_Comp=0 RBG_ProfComp=0 ProfComp=0 RandomLayerBG=0 RandomLayerBGBA=0 g1Rowk_of_inputsG=0 flowG_of_band=0 pad_subseq=0 BAfT=0 BAfE=0 BAEd=0 BAMO=0 ba_flowG=0 ba_domG=0 ba_mlout=0 ba_dom_of_bulk=0 ba_Ed_of_im=0 
```
Nondegeneracy: `N ≥ 2.1e6`, windows nonempty, `fT ∈ [cT,1)` strictly at every listed `n`; no `N=0`, empty index, collapsed window. The Lean statements are `∀ᶠ`: the first `n` at which the scale rows hold is astronomical (table, last row) at every `τU ≤ 1/720`; the merged band instance `inst_g1Rowk_of_inputs` (`RandomLayerB.lean:497`) has the same feature. No Lean witness depends on it.

### Fill-in table (CONTROL H250 (4)) and findings
| # | deliverable | line / n/a |
|---|---|---|
| (i) | exponent table | rows above (`κ'`, `c`, `cT`, `τD′`, thresholds, `ε`, `τU`) |
| (ii) | instance | band `band2.py`, BA `ba2.py`, V3 antecedent `v3.py` (above); "against probe B3": the same constants `κ_0`, `cT`, `η=N^{-19/20}` as probe `:301-326`; `ba2.py` is an independent numerical re-derivation of `S0` |
| (iii) | D1 compiled | n/a here, because compiling is the probe step. Math: predicate form `T2475_RBG_Comp` + `T2475_ProfComp` closes. Band: `bulk` is `|e| ≤ 2-κ` (`rfl`); `LLAt`/`QueAt`: `ouP=μ.prod gueP`, `Φ=(reindex sz φ)×id` is measure preserving (`seqP_reindex_preimage`, product with `id`), `ouMatC` agrees by `seqXmat_reindex` (`rfl`), integrand bounded measurable (`walk_measurable_Gres_apply`, `UNModel.meas`) so the integral transports; profile half `rfl` (`profPMTilde/profPPTilde` read `sz.L n`, `sz.lam n`, `sz.W n`). BA: same with `seqP (sz.withLam 0)` (`seqP_withLam_reindex_preimage`, `withLam_comp`; `seqHBA` and `mean=lam•PsiI` read `L,W,lam` at the index); bulk `BAbulk d (sz.L n)(sz.lam n)` `rfl`; profile half is a hypothesis (`P` is a variable until C3, owner C3). Law-level alternative: same content, adds fields (law map, `H` and `mean` equal) with no further consumer; recommend the predicate form plus one generic transport helper used by both discharges. Risk for the probe: transporting an integral along `Φ` needs AE-strong measurability of the integrand on the product space (bounded measurable entries, as above). |
| (iv) | D2 compiled | n/a here (probe step). Math: proof of `g1Rowk_of_inputsG` as in "Logic of D1/D2" with `rows_flow′`, `τD′=τU/4` (LL), `τU/2` (Q); band reading = `inst_g1Rowk_of_inputs` data (`sz0`, `1/6`, `1/10`, `τU=1/720`): table row `τU` and band2.py. Only premises: D1 and `Flow′, Dom′, Prod′, LL, Que′, T5`; none outside D1-D2 is needed (no bulk-nonemptiness, no `sz.lam` window) |
| (v) | copy table | `RandomLayerB:100-181` (82 lines: vocabulary 103-181) → `RBG_*` verbatim (probe `:34-69`), Bulk `:116-118` and `pad :182-200` dropped; `:203-239` (37) `oull_seq` → `oull_seq′` (take `κ',c,cT` from `Flow′`, `κ''` from `Dom′`, `τD′=τU/4`, `rows_flow′`); `:240-309` (70) `eq747_seq` → `eq747_seq′` (`τD′=τU/2`, same `ε`); `:311-341` (31) `g1Rowk_of_inputs` → `…G` (pad via `pad_subseq`, `comp_admissible`, `comp_size`); `RandomLayerA:98-150` (53) `rows_flow` → `rows_flow′` (hs: `cT ≤ t0`; `hs4 : √cT ≤ √t0`; `etaT`, `gueScale` replaced by `√t0·η`, `N√t0·η`; `r1,r2` with `N^{-τD′}√cT` as in the table); `rowsLL :213`, `rowsQ :335` reused uncopied |
| (vi) | band recovery | `Dom′`: `RandomLayerB_dom_band :376`, `κ'=κ`. `Prod′`: hypotheses of `RBG_Prod` do not give `Im z>0` (the inverse `(N√fT·Im z)⁻¹ ≤ N^{-τD}` is trivial for `Im z<0`), so `Ed` must carry the T1 identity `etaT(lemE z)(lemT z)=√(lemT z)·Im z`: band `EdId κ z := |lemE z| ≤ 2-κ ∧ etaT … = √(lemT z)·z.im`; then `RandomLayerB_prod_band :400` applies after rewriting `etaT`, `gueScale`. `Que′`: `RandomLayerB_Que_band :439` at `min κ κ'` (bulk is monotone in `κ`; `Ed κ'` first conjunct). Recommendation: keep `flowG_of_band` as pinned (plain `Ed`, probe `:71`), add one more public lemma for `EdId` (from the same `RandomLayerB_flow_band`, 4th conjunct = identity); the band reading of D2 uses `EdId` in all of `Flow′, Prod′, Que′` (one `Ed` per `g1Rowk_of_inputsG`). bridge kind: theorem recoveries (Part 4 `example`s become theorems) |
| (vii) | hypothesis table | `Flow′`: band `RandomLayerB_flow_band` / BA `ba_flowG` (leaf). `Dom′`: `…dom_band` / `ba_domG` (leaf). Compat: band `rfl`+transport / leaf target 13. `ProfComp`: band `rfl` / **C3** (`UNOUProfile.ba`). `Prod′`: `…prod_band` / **C5**. LL (T3): `…LL_band` / **C5**. `Que′`: `…Que_band` / **C5**. T5 under `ML →`: `…ML_band` / `ba_mlout` from `UNMLOutBA` = **V3** (registered `UNPins.lean:110`) |
| (viii) | scan preview | Premise `Prop`s in binders of the new public theorems: `RBG_Flow, RBG_Dom, RBG_Comp, RBG_ProfComp, RBG_Prod, RBG_Que, RandomLayerB_LL, RandomLayerB_MLout`, `UNMLOutBA`. Each non-registered one is the conclusion head of a theorem of the plan (`flowG_of_band*`, `ba_flowG`, `ba_domG`, band recoveries, `ba_mlout`, merged `RandomLayerB_LL_band`), `scanPremises` (`Test/Axioms.lean:447`) counts these as proved: expected registry lines **none**. Owner text `Test/Axioms.lean:172-173` becomes "BA: C5g (`g1Rowk_of_inputsG`, T2475) + BA-C5 (`RBG_Prod`, LL, `RBG_Que` at `UNKind.ba`) + BA-N2 (instance)". Not run (no Lean at 1a): confirm at the probe/1b |
| (ix) | layout | generic: imports `GUEPhase/RandomLayerB`, `Induction/SizesComp`, `Mathlib.Data.Nat.Nth`; closure +1 module, 0 `BA/*` (above). Leaf: `RandomLayerBG`, `BA/UNPins`, `BA/MReg` (+`FlowPins`, `MFixedPoint`, `Chain/Carrier`); importers of both: `RBM3D.lean` only; `RandomLayerB/A`, `OUInterfaceK`, `PinsK`, `SizesComp` not edited (no in-place edit found necessary) |
| (x) | lines | ticket estimates: generic 400/530/760, leaf 120/190/280 (copied or edited: `RandomLayerB` 82+37+70+31 plus `RandomLayerA` 53 = 273 lines; the design counts ≈295 for `:100-341` and `A:98-150`; new ≈135), stop line 2,000, 2.6× references 1,380/490, all below 2,000; not remeasured here |
| (xi) | name clash | grep above: 0 hits for all pinned names and the proposed `RBG_Comp`, `RBG_ProfComp`, `RandomLayerBG_pad_subseq` stem |

Findings. (1) T6 false at BA and the failures of T1 conj. 1, 2, 4, T1′ are the design's claims (`T2449-design.md:10`), not re-derived here; the repair above does not depend on them. (2) Band `Ed` must carry the identity (row vi). (3) The BA eventual thresholds in the last table row make the instance an eventual one only; astronomical `n` is inherent to `cT≈2.7e-4` and `τU ≤ 1/720`. (4) Directions in `T2475_RBG_Comp`: bulk goes `sz` at `φ j` to `sz.comp φ` at `j` (feeds the one-sequence lemma); `LLAt`/`QueAt` go back from `sz.comp φ` at `j` to `sz` at `φ j` (conclusion): exactly the two directions the padding uses.

Verdict (math), per target: 1-4 PASS (verbatim; premises satisfiable at the instance). 5 PASS (D1: predicate form + `ProfComp`; the BA half takes `ProfComp`, owner C3). 6 PASS (exponents close; thresholds above). 7 PASS (D2 as `T2475_g1Rowk_of_inputsG`, no premise outside D1-D2). 8 PASS with the `EdId` addition (row vi). 9-12 PASS (`κ'=c=(πκ)^5/2048`, `cT=κ'/(κ'+1)`, `BAMO`=conjuncts 1,5,4 of `UNMLOutBA`, `UNPins.lean:110-115`). 13 PASS given `ProfComp`. 14 PASS (instances above). Overall **PASS**.

## (a″) Probe compile — Mon Oct 12 22:45:15 UTC 2026

Probe step (design gate D1-D2). File `RBM3D/Probe/T2475Pins.lean` in `/Users/junyin/Lean_proof/RBM3D-wt/T2475`, branch `t/T2475`, commits `27bd70b2` (probe) and `efeab400` (one docstring line corrected, no line added), blob `646eddc61a0a858865ce7102bf4ea9cb80914394` (`git hash-object`; equal to the file the commands below ran on), 399 lines (limit 400), not imported by `RBM3D.lean`, not merged. Section (a) is untouched. `$S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2475`. `bash $S/verify.sh` (it writes `eq.lean`, `generic_only.lean`, `scan_*.lean` from the committed probe and from `docs/tickets/checks/T2475-check.lean`, then runs the lines below; output saved in `$S/verify.out`):
```
== probe ==
Mon Oct 12 22:44:15 UTC 2026
'RBM.Univ.GUEPhase.RBG_Comp_of_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.g1Rowk_of_inputsG_of_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.band_D2_at_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_flow_at_S0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_dom_ml_at_S0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_D2_at_S0' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
     399 RBM3D/Probe/T2475Pins.lean
== sorry/admit/axiom/native_decide ==
grep-exit=1 (1 = no hit)
== equivalences with the check file ==
exit=0
== generic part, imports RandomLayerB + SizesComp + Nat.Nth only ==
exit=0
== premise scan: main only ==
scan: 132 premises, unregistered: []
== premise scan: with the probe, scaffolding ignored ==
scan: 132 premises, unregistered: []
== premise scan: with the probe, nothing ignored ==
scan: 137 premises, unregistered: [RBM.Univ.GUEPhase.RBG_QueSeq,
 RBM.Univ.GUEPhase.RBG_LLSeq,
 RBM.BA.BAMO,
 RBM.Univ.GUEPhase.RBG_Eq747Seq,
 RBM.Univ.GUEPhase.RBG_OullSeq]
```
`git diff --stat main...t/T2475` shows the probe file only (399 insertions). `git --no-optional-locks diff --quiet ae791953 main -- <RandomLayerA/B, OUInterfaceK, PinsK, SizesComp, BA/UNPins, BA/MReg, BA/MFixedPoint, BA/FlowPins, Chain/Carrier, lean-toolchain, lake-manifest.json>`: exit 0 (worktree HEAD ae791953; `main` is ab435c6e). Meaning of the blocks: `exit=0`, no output: the probe elaborates; the seven `#print axioms` lines are its own; `eq.lean` is the probe followed by the check's Part 2-3 text under its own names `T2475_*` and `example`s `@T2475_RBG_Flow = @RBG_Flow := rfl` (also Dom, Prod, Que, Comp, `T2475_ProfComp`, D2 text `T2475_g1Rowk_of_inputsG = g1Rowk_of_inputsG_stmt := rfl`), `T2475_PadSubseq`, `T2475_FlowGOfBand`, `T2475_ba_dom_of_bulk/flowG/domG/mlout` inhabited by the probe's theorems, and the check's Part 4 band shapes (Comp, Dom, Prod with the identity datum, Que) and the BA shape of target 13 inhabited by `RBG_Comp_band`, `RBG_Dom_band`, `RBG_Prod_band`, `RBG_Que_band`, `ba_comp`.

Map of the probe (line numbers of the committed file): `27-58` `RBG_Flow`, `RBG_Dom`, `RBG_Prod`, `RBG_Que` (targets 1-4); `63` `pad_subseq`; `72`, `80` `RBG_Comp`, `RBG_ProfComp` (D1 text); `85-102` private transport and measurability helpers; `104-142` `RBG_Comp_of_law`; `147-175` `RBG_LLSeq`, `RBG_QueSeq`, `g1Rowk_pad` (D2 padding step); `177` `g1Rowk_of_inputsG_stmt` (D2 text); `194-213` `RBG_OullSeq`, `RBG_Eq747Seq`, `g1Rowk_of_inputsG_of_seq`; `224-277` band: `bandEd`, `flowG_of_band_id`, `flowG_of_band`, `RBG_Dom_band`, `RBG_ProfComp_band`, `RBG_Comp_band`, `RBG_Prod_band`, `RBG_Que_band`, `band_D2_at_sz0`; `291-348` BA: `BAfT`, `BAfE`, `BAEd`, `BAMO`, `ba_dom_of_bulk`, `ba_Ed_of_im`, `ba_flowG`, `ba_domG`, `ba_mlout`, `ba_comp`; `350-387` `ba_flow_at_S0`, `ba_dom_ml_at_S0`, `ba_D2_at_S0`. Mathlib/Lean names used and compiled: `Nat.nth_strictMono`, `Nat.nth_mem_of_infinite`, `Nat.frequently_atTop_iff_infinite`, `MeasureTheory.MeasurePreserving.prod`, `MeasurePreserving.id`, `MeasureTheory.integral_map`, `StrictMono.tendsto_atTop`, `Finset.measurable_sum`, `Complex.measurable_ofReal`.

### Filled table (every row; (a) rows are not repeated where unchanged)
| # | line / n/a |
|---|---|
| (i) | (a) row (i) unchanged. Lean-checked here: `ba_flowG` fixes `κ'=c=(πκ)^5/2048`, `cT=κ'/(κ'+1)`. `τD'` (`τU/4`, `τU/2`), the threshold `N^{τD-τD'} ≥ 1/(4√cT)`, `ε` of the eq747 window and `τU ≤ ouTauMax` are used only in the bodies of `oull_seq′`, `eq747_seq′`, which the probe does not contain; they stay checked by the numeric scripts of (a). |
| (ii) | (a) row (ii) unchanged (scripts `band2.py`, `ba2.py`, `v3.py`). Lean side: `band_D2_at_sz0` (`sz0`, `𝔠=1/6`, `𝔡=1/10`, `τU=ouTauMax`), `ba_flow_at_S0` (`S0`, `n=0`, `z=E_*+i/2`, no hypothesis), `ba_dom_ml_at_S0` (`ε=1/20`; `ba_mlout` at `sz0`, `zSeq`; `UNMLOutBA 3` a hypothesis), `ba_D2_at_S0`; the two `S0` instances are the T2449 probe `:301`, `:320` texts. |
| (iii) | D1 compiled. Form: predicate `RBG_Comp K P` + `RBG_ProfComp K P`, text of the check's Part 3 (`rfl`-equal, above). Both discharges go through one public helper `RBG_Comp_of_law` (hypotheses: bulk transfer; a measure preserving `R : SeqΩ sz → SeqΩ (sz.comp φ)` with `H j (R ω) = H (φ j) ω` and equal means). Band: `RBG_Comp_band`, `R = reindex sz φ`, `measurePreserving_reindex`, `H`, mean `rfl`, bulk `fun _ _ _ _ _ h => h`, profile half `RBG_ProfComp_band := ⟨rfl, rfl⟩`. BA: `ba_comp`, `R = reindex (sz.withLam 0) φ` (law `seqP (sz.withLam 0)`), same `rfl` facts, profile half the hypothesis `RBG_ProfComp (UNKind.ba d) P` (owner C3). The integral transport is `integral_map` on `Prod.map R id` (`MeasurePreserving.prod`); measurability from `walk_measurable_Gres_apply` and `measurable_ouMat`. The law-level form is not a second pin: it is the proof of the predicate. Padding step compiled: `pad_subseq`, `g1Rowk_pad`. |
| (iv) | D2 compiled: `g1Rowk_of_inputsG_stmt` (text of the check's Part 3, `rfl`-equal); `g1Rowk_pad` (`comp_admissible`, `comp_size` by `rfl`, `RBG_Comp`, `pad_subseq`); `g1Rowk_of_inputsG_of_seq : (∀ d, 3 ≤ d → RBG_OullSeq d) → (∀ d, 3 ≤ d → RBG_Eq747Seq d) → g1Rowk_of_inputsG_stmt`. `RBG_OullSeq`, `RBG_Eq747Seq` are the statements the 1b proves by copy-and-edit (`RandomLayerB_oull_seq :205`, `_eq747_seq :241`, `rows_flow′`); their proofs are not in the probe. Band reading `band_D2_at_sz0` and BA reading `ba_D2_at_S0` elaborate. |
| (v) | (a) row (v) unchanged; no copied body is in the probe except `pad_subseq` (T2449 probe `:79`), `ba_*` (T2449 probe `:87-148`, shortened), and the private measurability helper, which has the statement of the private `UnivMain_measurable_ouMatC` (`UnivMain.lean:373`) with a shorter proof (`ouMatC_eq_ouMat_add`, `measurable_ouMat`, `Measurable.add_const`). |
| (vi) | Compiled: `RBG_Dom_band` (`RandomLayerB_dom_band`, `κ'=κ`); `RBG_Prod_band` (`RandomLayerB_prod_band` after rewriting `etaT` by the identity and unfolding `gueScale`); `RBG_Que_band` (`RandomLayerB_Que_band` at `min κ κ'`); `flowG_of_band` as pinned (plain `Ed`, derived from `flowG_of_band_id`). The band datum is `bandEd κ _ _ z := |lemE z| ≤ 2 - κ ∧ etaT (lemE z) (lemT z) = √(lemT z) * z.im`; `band_D2_at_sz0` uses `flowG_of_band_id` (one `Ed` for `Flow′`, `Prod′`, `Que′`). Kind: theorems (bridge), not `example`s. |
| (vii) | `Flow′`: band `flowG_of_band_id RandomLayerB_flow_band`, BA `ba_flowG`. `Dom′`: `RBG_Dom_band`, `ba_domG`. Compat: `RBG_Comp_band`, `ba_comp` (+ `ProfComp`: band `RBG_ProfComp_band`, BA owner C3). `Prod′`: `RBG_Prod_band`, BA owner C5. LL: merged `RandomLayerB_LL_band`, BA owner C5. `Que′`: `RBG_Que_band`, BA owner C5. T5: `RandomLayerB_ML_band`, `ba_mlout` from `UNMLOutBA` (owner V3, registered). |
| (viii) | Scan run on the whole library plus the probe (blocks "premise scan" above): main alone 132 premises, none unregistered; probe with its scaffolding names ignored (`g1Rowk_of_inputsG_stmt`, `RBG_OullSeq`, `RBG_Eq747Seq`, `RBG_LLSeq`, `RBG_QueSeq`, `g1Rowk_pad`, `g1Rowk_of_inputsG_of_seq`, `band_D2_at_sz0`, `ba_D2_at_S0`): 132, none unregistered; nothing ignored: 137 premises, unregistered `RBG_QueSeq`, `RBG_LLSeq`, `RBG_Eq747Seq`, `RBG_OullSeq` and `BAMO` (a hypothesis head in `ba_D2_at_S0`). An earlier run, before `RBG_ProfComp_band` was a theorem of the probe, listed `RBG_ProfComp` as unregistered; the theorem removes it. Registry lines: none. For the 1b: `RBG_ProfComp_band` public; `g1Rowk_pad` and the one-sequence lemmas `private` (public, they would add the four premises listed). Owner text `Test/Axioms.lean:172-173` as in the ticket. |
| (ix) | `generic_only.lean` (probe lines `13-281` under a three-line header, imports `RandomLayerB`, `SizesComp`, `Mathlib.Data.Nat.Nth` only) exit 0: the generic file needs no `BA/*` import. Closure and importers: (a). No file outside the two new ones and the probe is touched. |
| (x) | Measured: generic block 262 lines (probe `20-281`), BA block 107 (`283-389`), scaffolding that does not enter the final file 20 (`194-213`). Final generic ≈ 262 − 20 + 160 (copied: 37 + 70 + 53 lines of (a) row (v)) = 402 before file header and docstring; BA ≈ 107 before header. Ticket estimates 400/530/760 and 120/190/280; stop line 2,000. |
| (xi) | `bash $S/clash2.sh` on `main` and the 20 branches matching `t/T246*`, `t/T247*` except `t/T2475`: 0 hits for every name in the Map (and `RBG_transport`, `RBG_meas_ouMatC`, `bandEd`, `g1Rowk_pad`, `RandomLayerBG`, `RandomLayerBGBA`, `g1Rowk_of_inputsG`, `pad_subseq`, `ba_t0_ineq`): `RBG_Flow=0 RBG_Dom=0 RBG_Prod=0 RBG_Que=0 RBG_Comp=0 RBG_ProfComp=0 RBG_Comp_of_law=0 bandEd=0 flowG_of_band=0 flowG_of_band_id=0 g1Rowk_of_inputsG=0 pad_subseq=0 ba_comp=0 BAfT=0 BAfE=0 BAEd=0 BAMO=0 ba_flowG=0 ba_domG=0 ba_mlout=0 ba_dom_of_bulk=0 ba_Ed_of_im=0 RandomLayerBG=0 RandomLayerBGBA=0` (full output `$S/clash2.out`). |

### Stop rules (ticket "Stop rules"), against this run
Targets 1-4: `rfl`-equal to the check. Targets 9-12: the check's `T2475_ba_*` are inhabited by the probe's theorems. A compatibility form closes at the band and at BA. `g1Rowk_of_inputsG_of_seq` uses no premise outside D1-D2 (no bulk nonemptiness, no `sz.lam` window, no BA profile fact beyond `RBG_ProfComp`). `UNG1Rowk`, U/V statements and merged pins are not changed; no edit of `RandomLayerA/B`, `OUInterfaceK`, `PinsK`, `SizesComp`, merged `BA/*`; no `private` deleted. The generic part imports no `BA/*`. File sizes far below 2,000. Not tested by Lean here: the proofs of `RBG_OullSeq`, `RBG_Eq747Seq` (1b), the C5 producers, `ProfComp` at BA (C3).

### Points for the 1a-audit
1. Pinned `flowG_of_band` (plain `Ed`, probe `:71`) compiles but cannot feed `Prod′`; the 1b needs `flowG_of_band_id`. Proposal: both public, pinned name unchanged. Alternative: the dispatcher re-pins `flowG_of_band` to `bandEd`.
2. `RBG_Comp_of_law` and `RBG_ProfComp_band` become public generic results (the first has the premise `RBG_ProfComp`, concluded by the second, so the scan stays quiet).
3. Paper-delta candidates: `T2475a` the subsequence argument (`pad_subseq` along `Nat.nth` of the bad `n`) that replaces T6 (bulk nonempty at every `n` or at none), false at BA; `T2475b` the band margin datum carries the T1 identity `etaT = √lemT · Im z` (Lean bookkeeping, no paper statement changes).

## (b) Stage 1b: script output — Mon Oct 12 23:09:51 UTC 2026 (`date -u`)
Branch `t/T2475`, HEAD `4d8de5b1`, 8 commits ahead of main (`git log --oneline main..HEAD`): probe `27bd70b2`, `efeab400` (unchanged: `git hash-object RBM3D/Probe/T2475Pins.lean` = `646eddc61a0a858865ce7102bf4ea9cb80914394`, the blob of (a″)), then `67fafd76`, `f644b986`, `3391c1f5`, `7e58dab0` (generic file by sections), `450c8986` (leaf), `4d8de5b1` (`RBM3D.lean`, `Test/Axioms.lean` owner text, lint tidy). `$S` = scratchpad `T2475/final`.
```
$ lake build RBM3D.Universality.GUEPhase.RandomLayerBG RBM3D.BA.RandomLayerBGBA 2>&1 | grep -v "exceeds the 100\|^$\|longLine" | tail -3
Build completed successfully (3862 jobs).
$ lake build   (full library, after the last commit; started 23:02:53, finished 23:03:52 by `date -u`; log fullbuild.out, filtered by grep)
info: RBM3D.lean:546:0: axiom audit: 13918 theorems, 4412 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4314 jobs).
exit=0
$ wc -l (each section commit: generic 192, 263, 433, 526; leaf 219; stop line 2,000 per file, none reached)
     526 RBM3D/Universality/GUEPhase/RandomLayerBG.lean
     219 RBM3D/BA/RandomLayerBGBA.lean
     745 total
$ lake env lean $S/axioms.lean 2>&1 | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"   (27 `#print axioms` in axioms.lean; `grep -vc` counts the other lines)
pretty-printed lines equal to the standard three: 27
other lines: 0
```
Names printed (prefix `RBM.`): `Univ.GUEPhase.RBG_Flow Univ.GUEPhase.RBG_Dom Univ.GUEPhase.RBG_Prod Univ.GUEPhase.RBG_Que Univ.GUEPhase.RBG_Comp Univ.GUEPhase.RBG_ProfComp Univ.GUEPhase.RandomLayerBG_pad_subseq Univ.GUEPhase.RandomLayerBG_Comp_of_law Univ.GUEPhase.g1Rowk_of_inputsG Univ.GUEPhase.RandomLayerBG_flowG_of_band_id Univ.GUEPhase.flowG_of_band Univ.GUEPhase.RandomLayerBG_dom_band Univ.GUEPhase.RandomLayerBG_profComp_band Univ.GUEPhase.RandomLayerBG_comp_band Univ.GUEPhase.RandomLayerBG_prod_band Univ.GUEPhase.RandomLayerBG_Que_band Univ.GUEPhase.RandomLayerBGInst.inst_g1Rowk_of_inputsG BA.BAfT BA.BAfE BA.BAEd BA.BAMO BA.ba_dom_of_bulk BA.ba_Ed_of_im BA.ba_flowG BA.ba_domG BA.ba_mlout BA.RandomLayerBGBA_comp`
`grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide'` on both files: no hit (grep-exit=1).

### Statements: extraction by script and diff (`python3 -I $S/stmtdiff.py`; whitespace-normalised; `T2475_` prefix removed from the check texts)
```
--- targets 1-4 and 5 (defs) against the check file Part 2/3 (T2475_ prefix removed)
RBG_Flow vs check: IDENTICAL (306 chars; file :59 vs reference :165)
RBG_Dom vs check: IDENTICAL (334 chars; file :65 vs reference :170)
RBG_Prod vs check: IDENTICAL (941 chars; file :72 vs reference :175)
RBG_Que vs check: IDENTICAL (1036 chars; file :87 vs reference :188)
RBG_Comp vs check: IDENTICAL (394 chars; file :115 vs reference :256)
RBG_ProfComp vs check: IDENTICAL (245 chars; file :123 vs reference :266)
--- target 5 (defs, pad_subseq) against the probe texts passed at the 1a-audit
RBG_Comp vs probe: IDENTICAL (394 chars; file :115 vs reference :72)
RBG_ProfComp vs probe: IDENTICAL (245 chars; file :123 vs reference :80)
pad_subseq: RandomLayerBG_pad_subseq vs probe pad_subseq: IDENTICAL (150 chars; file :105 vs reference :63)
--- target 7: statement of g1Rowk_of_inputsG (after the colon) vs probe g1Rowk_of_inputsG_stmt and vs check T2475_g1Rowk_of_inputsG
g1Rowk_of_inputsG vs probe stmt: IDENTICAL (787 chars; file :399 vs reference :177)
g1Rowk_of_inputsG vs check: IDENTICAL (787 chars; file :399 vs reference :275)
--- BA leaf statements (targets 9-12 and vocabulary) vs the probe
BAfT vs probe: IDENTICAL (91 chars; file :49 vs reference :291)
BAfE vs probe: IDENTICAL (94 chars; file :52 vs reference :292)
BAEd vs probe: IDENTICAL (155 chars; file :56 vs reference :293)
BAMO vs probe: IDENTICAL (229 chars; file :61 vs reference :295)
ba_dom_of_bulk vs probe: IDENTICAL (179 chars; file :69 vs reference :300)
ba_Ed_of_im vs probe: IDENTICAL (150 chars; file :87 vs reference :313)
ba_flowG vs probe: IDENTICAL (67 chars; file :92 vs reference :317)
ba_domG vs probe: IDENTICAL (89 chars; file :103 vs reference :327)
ba_mlout vs probe: IDENTICAL (136 chars; file :115 vs reference :337)
--- RandomLayerBGBA_comp (target 13) vs probe ba_comp
RandomLayerBGBA_comp vs ba_comp: IDENTICAL (134 chars; file :126 vs reference :345)
```
Targets 9-12 as extracted (the check's `T2475_ba_*` agree up to binder form, see the equivalences):
```
RandomLayerBGBA.lean:69 theorem ba_dom_of_bulk (d L : ℕ) [NeZero L] (g κ : ℝ) (hκ : 0 < κ) {z : ℂ} (hb : BAbulk d L g κ z.re) (h0 : 0 < z.im) (h1 : z.im ≤ 1) : (Real.pi * κ) ^ 5 / 2048 ≤ (BAm d L g z).im
RandomLayerBGBA.lean:92 theorem ba_flowG (d : ℕ) : RBG_Flow (UNKind.ba d) (BAEd d) (BAfT d)
RandomLayerBGBA.lean:103 theorem ba_domG (d : ℕ) : RBG_Dom (UNKind.ba d) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
RandomLayerBGBA.lean:115 theorem ba_mlout (d : ℕ) (hd : 3 ≤ d) (h : UNMLOutBA d) : RandomLayerB_MLout (BAfT d) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (BAMO d)
```
Equivalences stated and compiled (`lake env lean $S/eqv.lean`, exit=0, 19 `example`s: check Part 2-3 text + `RBG_X ↔ T2475_RBG_X := Iff.rfl` for X = Flow, Dom, Prod, Que, Comp, `RBG_ProfComp ↔ T2475_ProfComp`, `T2475_PadSubseq := RandomLayerBG_pad_subseq`, `T2475_FlowGOfBand d := flowG_of_band`, `T2475_g1Rowk_of_inputsG := g1Rowk_of_inputsG`, `T2475_ba_dom_of_bulk := @ba_dom_of_bulk`, `T2475_ba_flowG/_domG/_mlout := ba_flowG/_domG/_mlout` (binder-adjusted), `BAEd = T2475_BAEd`, `BAMO = T2475_BAMO` by `rfl`, and the Part 4 shapes for target 13, band Comp+ProfComp, band Dom, and the D2 band reading).
D1 text = `RandomLayerBG.lean:113-125` (probe `:72-82`), `RandomLayerBG_pad_subseq` `:105` (probe `:63`); D2 text = `:399-413` (probe `g1Rowk_of_inputsG_stmt` `:177-191`); both IDENTICAL above. D2 binders: `K P ML Loc Que Ed fE fT Fl MO KF PB`, then `RBG_Flow`, `RBG_Dom`, `RBG_Comp`, `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que`, `ML → RandomLayerB_MLout`; conclusion `UNG1Rowk K P ML Loc Que`.

### Compiled nonempty instances (all in the built files; deterministic premises discharged)
- Target 8, band, `d = 3`, `sz0`, `𝔠 = 1/6`, `𝔡 = 1/10`, `τU = ouTauMax`: `RandomLayerBGInst.inst_g1Rowk_of_inputsG` (`RandomLayerBG.lean:509`), the application of `g1Rowk_of_inputsG` to `RandomLayerBG_flowG_of_band_id RandomLayerB_flow_band`, `…_dom_band`, `…_comp_band`, `…_prod_band`, `RandomLayerB_LL_band`, `…_Que_band`, `RandomLayerB_ML_band`; hypotheses `UNMLOut`, `UNLocAvgBand`, `UNQueBand` (other gates). Its conclusion is `UNOULLk ∧ UNOUEq747k` at `sz0`, as `inst_g1Rowk_of_inputs`.
- Target 14, BA, `d = 3` (`RandomLayerBGBA.lean`): `:144` `Flow′` at `S0`, `n = 0`, `z = E_* + i/2` (hypothesis-free); `:151` `Flow′` at `S0`, every `n`, `Im z = N^{-19/20}`; `:162` `Dom′` at `S0` (`ε = 1/20`, `E ≡ E_*`, `η_n = N^{-1+ε}`) then T5 along that flow at `t_n ≡ cT` (conclusion `BAFlow … ∧ BAMO …`; hypothesis `UNMLOutBA 3`); `:186` T5 at `sz0`, `zSeq`, `t_n ≡ 1/2` (conclusion `BAMO 3 sz0 zSeq _`); `:191` target 13 at `S0`, `φ = (2 * ·)` (hypotheses `P`, `RBG_ProfComp`: C3); `:201` the BA reading of D2 at `S0` (hypotheses: `RBG_ProfComp`, `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` at BA = C3/C5, `UNMLOutBA`, `UNLocAvgBA`, `UNQueBA`).

### Copy table (ports are inside RBM3D; RBM1D/RBM2D were not read or used, so no `diff --stat` for them)
| source (main) | new name (this branch) | edit |
|---|---|---|
| `RandomLayerB:100-181` T1, T1', T2, T4 vocabulary | `RBG_Flow/Dom/Prod/Que` `:59-98` | the check's Part 2 texts: `Ed κ'`, `cT`, `√fT Im z` (verbatim, diff above) |
| `RandomLayerB:116-118` T6, `:184-200` `RandomLayerB_pad` | `RandomLayerBG_pad_subseq` `:105`, `RBG_Comp`, `RBG_ProfComp` `:115-123` | dropped; padding along `Nat.nth` of the bad `n` |
| private `UnivMain_measurable_ouMatC` (`UnivMain.lean:373`) | `RandomLayerBG_meas_ouMatC` `:140` | shorter proof (`ouMatC_eq_ouMat_add`) |
| `RandomLayerA:98-144` `RandomLayer_rows_flow` | `RandomLayerBG_rows_flow` `:216` | `1/16 ≤ t₀` ↦ `cT ≤ t₀`; `etaT`, `gueScale` ↦ `√t₀ η`, `N √t₀ η`; `r1`, `r2` at `√cT η` (`√cT ≤ √t₀`) |
| (new) | `RandomLayerBG_scale` `:192` | `N^{-b}η/4`, `4(Nη)⁻¹ ≤ N^{-b}` ⟹ `N^{-a}√cT η`, `(N√cT η)⁻¹ ≤ N^{-a}` once `(4√cT)⁻¹ ≤ N^{b-a}` |
| `RandomLayerB:204-236` `oull_seq` | `RandomLayerBG_oull_seq` `:265` | `κ'`,`c`,`cT` from `Flow′`, `κ''` from `Dom′`; `rowsLL` (reused, `τU/2`) ↦ `τD' = τU/4`; `Prod′` at `(κ', τU/4)` |
| `RandomLayerB:238-307` `eq747_seq` | `RandomLayerBG_eq747_seq` `:313` | same; `rowsQ` (reused, `τU`) ↦ `τD' = τU/2`; `Que′` at `(κ, κ')`; window `ε = min(𝔠(𝔡-𝔡/3),1)` as merged |
| `RandomLayerB:311-341` `g1Rowk_of_inputs` | `g1Rowk_of_inputsG` `:399` | `pad_subseq` + `comp_admissible` (`SizesComp:93`) + `comp_size` (`rfl`) + `RBG_Comp`; no T6 |
| `RandomLayerB:351-451` `…_band` | `RandomLayerBG_*_band` `:441-493` | `bandEd` carries `etaT = √lemT Im z`; `Que′` via `min κ κ'` |
Probe → final renames (unpinned public names take the stem, §3 (E), audit O3): `bandEd` → `RandomLayerBG_bandEd`, `flowG_of_band_id` → `RandomLayerBG_flowG_of_band_id`, `RBG_Dom_band/_ProfComp_band/_Comp_band/_Prod_band/_Que_band` → `RandomLayerBG_dom_band/_profComp_band/_comp_band/_prod_band/_Que_band`, `RBG_Comp_of_law` → `RandomLayerBG_Comp_of_law`, `pad_subseq` → `RandomLayerBG_pad_subseq`, `ba_comp` → `RandomLayerBGBA_comp`, `ba_t0_ineq` → private `RandomLayerBGBA_t0_ineq`; probe scaffolding `RBG_LLSeq`, `RBG_QueSeq`, `RBG_OullSeq`, `RBG_Eq747Seq`, `g1Rowk_pad`, `g1Rowk_of_inputsG_stmt`, `g1Rowk_of_inputsG_of_seq` is gone (the two one-sequence lemmas are private theorems).

### Hypothesis table (premise of `g1Rowk_of_inputsG` → band discharge → BA source / owner)
| premise | band | BA |
|---|---|---|
| `RBG_Flow` | `RandomLayerBG_flowG_of_band_id RandomLayerB_flow_band`; plain datum: `flowG_of_band` | `ba_flowG` (leaf) |
| `RBG_Dom` | `RandomLayerBG_dom_band` | `ba_domG` (leaf) |
| `RBG_Comp` | `RandomLayerBG_comp_band` (`RandomLayerBG_Comp_of_law`, `RandomLayerBG_profComp_band`) | `RandomLayerBGBA_comp`; needs `RBG_ProfComp (UNKind.ba d) P`: owner C3 |
| `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` | `RandomLayerBG_prod_band`, merged `RandomLayerB_LL_band`, `RandomLayerBG_Que_band` | C5 (hypotheses of the BA example `:201`) |
| `ML → RandomLayerB_MLout` | merged `RandomLayerB_ML_band` | `ba_mlout` from `UNMLOutBA` (V3; `Test/Axioms.lean:185`) |

### Registry and premise scan
```
$ git diff -U0 main...t/T2475 -- RBM3D/Test/Axioms.lean | grep '^[-+] ' | grep -o 'BA: [^;]*(instance)'   (lines :172, :173; comment text only)
- BA: BA-C5 (T inputs) + BA-N2 (instance)
- BA: BA-C5 (T inputs) + BA-N2 (instance)
+ BA: C5g (`g1Rowk_of_inputsG`, T2475) + BA-C5 (`RBG_Prod`, LL, `RBG_Que` at `UNKind.ba`) + BA-N2 (instance)
+ BA: C5g (`g1Rowk_of_inputsG`, T2475) + BA-C5 (`RBG_Prod`, LL, `RBG_Que` at `UNKind.ba`) + BA-N2 (instance)
$ lake env lean $S/../scan_base.lean   [8-line `run_cmd` calling `RBM.Audit.scanPremises`] (import RBM3D, whole library incl. both new files; scanPremises, nothing ignored)
scan: 132 premises, unregistered: []
```
Registry lines added: none (every new premise `Prop` is the conclusion head of a theorem of this branch: `RBG_Flow/Dom/Comp/Prod/Que`, `RBG_ProfComp` by the band theorems; `UNMLOutBA` is registered). The full `lake build` above ran `#assert_rbm_axioms` (`axiom audit: 13918 theorems, 4412 definitions, 0 axioms`), whose unregistered-premise check passed.

### Greps, layering, diff
```
$ python3 -I (classify each hit of grep -nE "lemE|lemT|msc|etaT|gueScale|STFlow|2 - κ|BA[A-Za-z]" RandomLayerBG.lean as comment/code; band section starts at line 431)
before line 431 (generic part): 12 hits, 12 in comments, 0 in code
from line 431 (band section, target 8, and instance): 20 hits, 9 in comments, 11 in code
$ grep -n '^import RBM3D.BA' RBM3D/Universality/GUEPhase/RandomLayerBG.lean ; echo grep-exit=$?     -> (no output) grep-exit=1
$ import closure of RandomLayerBG (script over the import lines): 139 RBM3D modules; BA/* modules: []   (leaf: 158 modules, 9 of them BA/*, itself included)
$ git grep -n "GUEPhase.RandomLayerBG" -- 'RBM3D/*.lean' 'RBM3D.lean'  -> RBM3D.lean:542, RBM3D/BA/RandomLayerBGBA.lean:6 (importers; the third hit, leaf `:16`, is its docstring); the leaf is imported only by RBM3D.lean:543
$ git diff --stat main...t/T2475
 RBM3D.lean                                     |   2 +
 RBM3D/BA/RandomLayerBGBA.lean                  | 219 ++++++++++
 RBM3D/Probe/T2475Pins.lean                     | 399 +++++++++++++++++++
 RBM3D/Test/Axioms.lean                         |   4 +-
 RBM3D/Universality/GUEPhase/RandomLayerBG.lean | 526 +++++++++++++++++++++++++
 5 files changed, 1148 insertions(+), 2 deletions(-)
$ git diff main...t/T2475 -- RBM3D/Universality/GUEPhase/RandomLayerB.lean RBM3D/Universality/GUEPhase/RandomLayerA.lean RBM3D/Universality/OUInterfaceK.lean RBM3D/Universality/PinsK.lean RBM3D/Induction | wc -l  -> 0 ;  git diff --name-only main...t/T2475 -- RBM3D/BA/ -> RBM3D/BA/RandomLayerBGBA.lean
```
### `band_terminal`, `bUniv_holds` (`$S/bt.lean`, run in the branch worktree and in the main worktree at `ab435c6e`; `diff` of the two outputs: IDENTICAL)
```
-- branch:
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-- main:
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
diff: IDENTICAL
```
### Name-clash grep (`bash $S/clash.sh`; every final name, `git grep -nwF` on main and 30 branches `t/T245x…T249x` except `t/T2475`, pathspec `:!RBM3D/Probe`)
```
refs scanned:       31 (main + t/T245x..T249x except t/T2475); pathspec RBM3D/*.lean RBM3D.lean, :!RBM3D/Probe
RBG_Flow=0 RBG_Dom=0 RBG_Prod=0 RBG_Que=0 RBG_Comp=0 RBG_ProfComp=0 RandomLayerBG_pad_subseq=0 RandomLayerBG_Comp_of_law=0 RandomLayerBG_transport=0 RandomLayerBG_meas_ouMatC=0 RandomLayerBG_scale=0 RandomLayerBG_rows_flow=0 RandomLayerBG_oull_seq=0 RandomLayerBG_eq747_seq=0 g1Rowk_of_inputsG=0 RandomLayerBG_bandEd=0 RandomLayerBG_flowG_of_band_id=0 flowG_of_band=0 RandomLayerBG_dom_band=0 RandomLayerBG_profComp_band=0 RandomLayerBG_comp_band=0 RandomLayerBG_prod_band=0 RandomLayerBG_Que_band=0 RandomLayerBGInst=0 inst_g1Rowk_of_inputsG=0 BAfT=0 BAfE=0 BAEd=0 BAMO=0 ba_flowG=0 ba_domG=0 ba_mlout=0 ba_dom_of_bulk=0 ba_Ed_of_im=0 RandomLayerBGBA_comp=0 RandomLayerBGBA_t0_ineq=0 RandomLayerBGBA_hg=0 RandomLayerBG=0 RandomLayerBGBA=0 
```
### Narrative
1. Generic file: 526 lines (ticket estimate 400/530/760); leaf: 219 (120/190/280); total 745 (520/720/1,040). No stop rule fired; no edit of `RandomLayerA/B`, `OUInterfaceK`, `PinsK`, `Induction/SizesComp`, merged `BA/*`; no `private` deleted; `UNG1Rowk` and U/V statements unchanged.
2. `Prod′`, `Que′` exponents. `rowsLL` gives `t ≤ N^{-τU/2}η/4` and `4(Nη)⁻¹ ≤ N^{-τU/2}`; with `√fT ≥ √cT` the `Prod′` rows at `τD' = τU/4` (LL) and `τU/2` (Que) hold once `N^{τU/4}` (resp. `N^{τU/2}`) `≥ (4√cT)⁻¹`, eventually since `Nsz → ∞` (`hA.2.2.1`). At BA (`cT ≈ 2.7e-4`, (a)) the first such `n` is astronomical (`log10 N ≥ 3401.4`, (a) table); at the band `4√cT = 1`. Both are `∀ᶠ` statements; no Lean witness uses that `n`.
3. D1/D2 as passed at the 1a-audit; the law-level form is the proof (`RandomLayerBG_Comp_of_law`), not a second pin. `g1Rowk_of_inputsG` is a theorem whose statement text equals the probe's `g1Rowk_of_inputsG_stmt`.
4. Audit observations: O1 (plain-`Ed` `Que′` shape): not needed, `RandomLayerBG_Que_band` is at `RandomLayerBG_bandEd`; O2: the BA `Dom′`/T5 instance concludes `BAFlow … ∧ BAMO …` (no `True`); O3: stems (rename map above); O4: the BA D2 reading and the BA T5/`Dom′` instances are `example`s, one-sequence lemmas are private, so `BAMO`, `RBG_*Seq` do not enter the scan; O5: `T2449b` below.
5. Section (a) is untouched; no (a′) was needed.

## (c) Verified Mathlib names (all compiled in the files above)
`Nat.nth_strictMono`, `Nat.nth_mem_of_infinite`, `Nat.frequently_atTop_iff_infinite`, `Set.ofPred`, `Filter.not_eventually`, `StrictMono.tendsto_atTop`, `MeasureTheory.MeasurePreserving.prod`, `MeasurePreserving.id`, `MeasureTheory.integral_map`, `Finset.measurable_sum`, `Complex.measurable_ofReal`, `Real.rpow_neg`, `Real.rpow_add`, `Real.rpow_pos_of_pos`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.sqrt_le_sqrt`, `Real.sqrt_pos`, `inv_le_comm₀`, `inv_anti₀`, `tendsto_rpow_atTop`, `div_le_div_iff₀`, `div_le_div_of_nonneg_left`. Names verified absent: none looked up.

## (d) Open issues and paper-delta candidates
- Open: `RBG_ProfComp (UNKind.ba d) P` is C3's (with `UNOUProfile.ba`); `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` at `UNKind.ba` are C5's; `UNMLOutBA` is V3's. None has a ledger line (the scan counts the band theorems as proving the `Prop`s); the owners are named in the `UNOULLk`/`UNG1Rowk` owner text and in the hypothesis table.
- `T2449b` (lands with this row; the 1a-audit found it as D689 (b), `docs/paper-deltas.md:1653`): the UN-51 interface Flow, Dom, Bulk is false at BA; the repaired inputs `RBG_*` carry `κ' = (πκ)^5/2048` (`ba_flowG`, `ba_domG`), `cT = κ'/(κ'+1)` for `1/16`, `η_{t₀} := √fT Im z`; the `|Re z| ≤ 2-κ` of `zztE_BA` is the T2001g typo.
- `T2475a`: the subsequence argument (`RandomLayerBG_pad_subseq` along `Nat.nth` of the bad `n`, one-sequence lemmas on `sz.comp φ`) replaces T6 (bulk nonempty at every `n` or at none), false at BA.
- `T2475b`: the band margin datum `RandomLayerBG_bandEd` carries the T1 identity `etaT = √lemT · Im z` (Lean bookkeeping; `RBG_Prod` has no `Im z > 0`).
- `T2475c`: `Prod′` is applied at `τD' = τU/4` (LL) and `τU/2` (Que), and the rows are stated at the scale `√cT η`; internal exponents, no paper statement changes.
