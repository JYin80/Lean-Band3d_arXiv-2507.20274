Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 22:49:36 UTC 2026
Base `main` ab435c6e (differs from the worktree `t/T2473` = eaa247c4 only in docs and the docstring of `Chain/CltGen.lean`, which no file read here imports; `git diff --name-only eaa247c4 ab435c6e`). Merged inputs: T2474 (e8fd7d27+eaa247c4), T2471 (51e233bd+ae791953), T2467 (97341078), T2453, T2454, T7a, U3s1. Scratch (python only) in the session scratchpad `T2473/`: `inst2.py d1.py d3.py priv.py clash.sh`. No Lean written. Target 6 is T2474's (dropped, answer (1)).
**Decisions.** (1) D1 picks route **(a) for every layer** (census below): **the pre-signed switch of the probe step to `prover-max` is NOT fired.** Every band-only declaration found by the census (iii) has a field in W / S / K / LoopForm / `DecayGen_Spec` or a merged generic pin. The one block with no field is the initial membership (7 declarations, `AzumaProxyN:340-945`): by answer (5) it is target 9's inline hypothesis, not a route-(b) layer, and its BA source is absent (vi). (2) Targets 1-5, 7, 8, 10, 11 PASS; 9 PASS with an owed BA item (T4-BA). (3) Three flags for the dispatcher at the 1a-audit, none a RETURN: **F1** D3 gives own central 4,029 > 3,900 (third row, short REQ); **F2** target 4 takes the law of the grid state as T2467's merged `Step2EventsGen_Law` (one text, X1-C4) instead of the check file's W conjuncts for `μ`, `Hf`; **F3** target 5 needs the premise `Im m ≤ 1`.
### (i) Exponent table (k = 3, τ' = 1/5, τ_K = 1/10, D_t = D = D₁ = 1, ε = 1/10, N = (WL)^3)
| quantity | value | constraint (source) | slack |
|---|---|---|---|
| C_K | 64 | rows A `8+(4k+8)(1-τ')+2D_t`=26.0, B `3+4τ_K+5k(1-τ')+D_t`=16.4, C `2(1-τ')+τ_K+2k(1-τ')+D_t`=7.5, D `1-τ'`=0.8 (`GridEnvelopeN:595`); `D₁+4D+k+2C_P+8 ≤ C_K` (`GridAssemblyN:227`) | binding row = AssembledN: 63.6 ≤ 64, slack 0.4; rows A-D ≥ 38 |
| C_P | `11+(4k+4)max(0,1-τ')` = 23.8 (`AzumaProxyN2:33,905`) | fixed before K; `P ≤ N^{C_P}`; the X-moments are walk facts and `gvarF ≤ 1` holds for every real g′ and 3 ≤ L (`AzumaProxyN2:227`) | independent of g′, d (identity) |
| D₁ | 1 (any) | `8 N^{C_K+k} e^{-N^{2ε}/4} ≤ N^{-D₁}` ⇐ `N^{2ε}/4 ≥ (D₁+C_K+k) ln N + ln 8` (my union count of the tail `4e^{-x²/(4Σc)}` of `stoppedAzumaZN`, `GridAssemblyN:1014`, over K ≤ 2N^{C_K}, N^k labels; the constant in `gridAsm_core` :1378 is not re-derived) | eventual: first n = 6 (N = 10^21.5); n = 10: 2.58e4 vs 3.93e3 (6.6×) |
| τ_K | 1/10 | any > 0; K-window `‖KI‖ ≤ N^{τ_K} η^{-m}` (`exists_norm_KI_le_wing`, `HierDriftGen:1083`) | enters row B as 4τ_K; row B slack 47.6 |
| RangeCond window | `1-t ≥ N^{-(1-τ')}` (`Green/Pins:55`), t = 1/16 ≤ T0 | band lemT(z₀) = 0.99999; BA T0 ∈ [0.69, 0.70] ≥ 2/3 (`t0_sz0`, `BA/FlowPins:1227`) | 15/16 vs 8.8e-6 (n = 0), 8.8e-21 (n = 10) |
| `(1+(1-u_m)^{-1})^k` | ≤ 8.83 (u_m ≤ 1/16); ≤ `(1+N^{1-τ'})^k` | K2: `Σ_b‖uKer_{v,w}‖ ≤ (1-v)/(1-w) ≤ (1-w)^{-1} ≤ 1+(1-w)^{-1}` per slot, 0 ≤ v ≤ w < 1 | 1 per slot |
| Γ = N^ε | 4.29 / 14.9 / 321 (n = 0, 1, 10) | ε > 0 arbitrary; `K+1 ≤ N^C` and failure `N^{-D}` per index, D > C | K = 4: C = 1; K_n = ⌈N^64⌉: C = 65, D = 70: `N^{-5}` = 10^-31.6 / -58.7 / -125.3 |
| `B_{t,0}`, `c_d` | 3.3e-5 (n = 0) ≤ 1 | `STConStInd c_d`: `B^{c_d} ≤ (1-t)/(1-s)` (`Defs:168`), c_d = 1/100; (D2) arithmetic `B^{1/6} ≤ 1` | 0.902 ≤ 0.9375 (n = 0, binding), 0.629 (n = 10) |
| admissibility | 𝔠 = 1/6, 𝔡 = 1/10 | `N^{1/6} = √(WL) ≤ W` ⇐ L ≤ W (`sz0_L_le_W`, `Sizes:272`); absorption `N^𝔠 W^{-(D'+1)} ≤ W^{-D'}` (`GridGoodN:541`) | n = 0: 11.31 vs 32 |
| spectral window | band κ = 1/10, κ_m = √κ/2 = 0.158; BA κ_m = 1/2 | `DecayGen_Spec`: κ_m ≤ Im m (`DecayGen:91`); new premise `Im m ≤ 1` (F3: `η ≤ 1-v` in `exists_norm_KI_le_wing`) | Im m = 0.968 (band), 0.8325 (BA): 0.81 / 0.33 |
| E′ reduction (target 5 sums) | `E′_n = 2√(1-(Im m_n)²)`, `(mE E′).im = Im m`, `abs E′ ≤ 2-κ_m²` | `stepErrN` reads E only through `etaT` (`GridDriftN:289`, `Path/OneStep:78`), so `stepErrNg = stepErrN … E′` and the band `sum_weighted_stepErrN_le` (`GridEnvelopeN:613`) applies | band: E′ = 0.5 = E; 2-κ_m²-abs E′ = 1.475 |
### (ii) One concrete instance (d = 3, sz0, band `z0` = 1/2 + iN^{-4/5} and BA `flow_sz0`, s ≡ 0, t ≡ 1/16)
Command: `cd $S/T2473 && python3 -I inst2.py` (`$S` = the session scratchpad). Output verbatim:
```
k=3 eps=0.1 tau'=0.2 tauK=0.1 D_t=1.0 D=1.0 D1=1.0 s=0 t=1/16 cd=1/100; C_P=23.8; rows A-D=[26.0, 16.4, 7.5, 0.8]; D1+4D+k+2C_P+8=63.6 <= C_K=64
n=0: L=4 W=32 lam=0.0156 N=10^6.32; K_n=ceil(N^64) ~10^405, Delta=(t-s)/K_n ~10^-405; [GridGood data K=4: Delta=1/64, 5<=N]
   Gamma=N^eps=4.29; N^(1/6)=11.31<=W True; B_(t,0)=3.3e-05<=1 True; B^cd=0.902<=(1-t)/(1-s)=0.9375 True; RangeCond 15/16>=N^-(1-tp)=8.8e-06 True; (1+(1-u_m)^-1)^k<=8.83
   BAND (z0=1/2+iN^-4/5): lemT=0.999991>=t True; Im m=0.9682 in [k_m=0.158,1] True; eta_0=0.9682, eta_t=0.9077; E'=2sqrt(1-Imm^2)=0.5000, |E'|<=2-k_m^2 True
   BA (flow_sz0, w=6i/5): Im m=0.83249 in [4/5,5/6] True, T0=0.6937>=2/3 True >=t True, lam0=sqrt(T0)*lam=0.013>0, k_m=1/2<=Im m True; eta_0=0.8325, eta_t=0.7805
   limits: union bound (K_n+1)N^-70 ~ N^-5 = 10^-31.6; Azuma tail N^(2eps)/4=4.59 >= (D1+C_K+k)lnN+ln8=992: False
n=1: L=8 W=1024 lam=0.000244 N=10^11.74; K_n=ceil(N^64) ~10^751, Delta=(t-s)/K_n ~10^-751; [GridGood data K=4: Delta=1/64, 5<=N]
   Gamma=N^eps=14.9; N^(1/6)=90.51<=W True; B_(t,0)=1e-09<=1 True; B^cd=0.813<=(1-t)/(1-s)=0.9375 True; RangeCond 15/16>=N^-(1-tp)=4.1e-10 True; (1+(1-u_m)^-1)^k<=8.83
   BAND (z0=1/2+iN^-4/5): lemT=1.000000>=t True; Im m=0.9682 in [k_m=0.158,1] True; eta_0=0.9682, eta_t=0.9077; E'=2sqrt(1-Imm^2)=0.5000, |E'|<=2-k_m^2 True
   BA (flow_sz0, w=6i/5): Im m=0.83333 in [4/5,5/6] True, T0=0.6944>=2/3 True >=t True, lam0=sqrt(T0)*lam=0.000203>0, k_m=1/2<=Im m True; eta_0=0.8333, eta_t=0.7812
   limits: union bound (K_n+1)N^-70 ~ N^-5 = 10^-58.7; Azuma tail N^(2eps)/4=55.7 >= (D1+C_K+k)lnN+ln8=1.84e+03: False
n=10: L=44 W=5153632 lam=8.82e-09 N=10^25.07; K_n=ceil(N^64) ~10^1604, Delta=(t-s)/K_n ~10^-1604; [GridGood data K=4: Delta=1/64, 5<=N]
   Gamma=N^eps=321; N^(1/6)=1.506e+04<=W True; B_(t,0)=7.8e-21<=1 True; B^cd=0.629<=(1-t)/(1-s)=0.9375 True; RangeCond 15/16>=N^-(1-tp)=8.8e-21 True; (1+(1-u_m)^-1)^k<=8.83
   BAND (z0=1/2+iN^-4/5): lemT=1.000000>=t True; Im m=0.9682 in [k_m=0.158,1] True; eta_0=0.9682, eta_t=0.9077; E'=2sqrt(1-Imm^2)=0.5000, |E'|<=2-k_m^2 True
   BA (flow_sz0, w=6i/5): Im m=0.83333 in [4/5,5/6] True, T0=0.6944>=2/3 True >=t True, lam0=sqrt(T0)*lam=7.35e-09>0, k_m=1/2<=Im m True; eta_0=0.8333, eta_t=0.7813
   limits: union bound (K_n+1)N^-70 ~ N^-5 = 10^-125.3; Azuma tail N^(2eps)/4=2.58e+04 >= (D1+C_K+k)lnN+ln8=3.93e+03: True
first n with the Azuma-tail inequality (eventual): n=6, N=10^21.53; holds at n=10
```
Reading. Hypotheses checked at n = 0, 1, 10: `0 ≤ s < t ≤ T0 < 1`, `K ≠ 0`, `K+1 ≤ N^C`, `B ≤ 1`, `STConStInd`, `RangeCond`, admissibility, `κ_m ≤ Im m ≤ 1`, `lam0 > 0` (BA), `η > 0` on the window; the grid data are K = 4 (GridGood) and K_n = ⌈N^64⌉ (Envelope, Assembled; forced by the pin). The `fail` of the Azuma line at n = 0, 1 is the conclusion's eventual threshold (the pins say `∀ᶠ n`). External hypotheses (the ≺ statements `STSEforLnConclgL`, `STEKDecaygL`, `STKboundgL`, `STKwardgL`, `STDecayLoopUgL`): each is a `∀ D` polynomial-probability statement, so the only limits owed are the two `limits:` lines (union bound, Azuma tail); band discharges are merged theorems (table below); BA ones are owed (U2-BA, T1-BA, BA-V). `GridDriftNg` is not external: T2474's `gridDriftNg` proves it from its classes.
### (iii) D1 census (script `d1.py`: distinct outside declarations read, privates included, by class; K kernel, W walk, S per-step, M model-free, B band-only)
`GridGoodN {B:32 M:40 W:7}  GridEnvelopeN {B:7 M:19 W:2}  GridAssemblyN {B:3 M:30 S:11 W:11 K:6}  AzumaProxyN {B:19 M:57 W:12 K:7 S:17}  AzumaProxyN2 {B:7 M:41 W:15 K:8 S:16}`
B → field: pins `Lloop STKloop STLK STKbound STKward STIngR STStep2Concl STSEforLnConcl STDecayLoopU stDecayLoopU_of_step2 stEtermDecay stSEforLn_holds STmaxL STXiL…` → merged U3s1/T7a pins (hypotheses); `STLIM STLKIM STavgErrM STegtM STelklkM STksimLKM STeeM STeeLoop` → T8b `STLIMg … STeeMg`; `zt etaT etaT_pos mE mE_im mE_im_pos lemT lemT_lt_one abs_lemE_le STflowE` → `Cm.eta`, `Cm.m`, `DecayGen_Spec`, LoopForm (`ztOf`); `KLK` → `Cm.KI`, `HierDriftGen_KLink`; `Ugen uKer cycProd mSigma norm_mSigma mE_mul norm_cycProd` → `Step2Gen_UN/uKer` + K1-K4; `SB norm_SB sbKernelR*` → walk variance (`gvarF`, any g′) and `Cm.S` row sums (T2474 `hS`); `sInst tInst Einst z0 flow_z0 Kg vg` → instance sections only; `initialGreenScalar initialLoopValue adjacentBlockWeight KLK_one KLK_isKLoop Bparam norm_mE` → initial membership (no field).
**Route: (a) for GridGood, Envelope, Assembly, AzumaProxy.** W = `StepDecompGen_WalkForm Cm lam' Ψ` (`StepDecompGen:73`, T2474) at targets 7-10 only (target 4 uses the law instead) (`azumaSubGN` holds at any `sz`, so `azumaSubGNg` is the band theorem at `sz.withLam lam'` with the test family shifted by Ψ: `StepDecompGen_hermTestFun_shift` :133, `loopFamShift_hermTestFun` :713). S = `hermTestFunLoopNOf` :101, `qvPropagatedNg` :505 (theorems, T2474). Compat = `StepDecompGen_LoopForm Cm E` (:60: `LM = loopFine`, `LIM = loopL (blockMat H)`, `eta = etaOf`; measurability of `LM`, `LIM` in H by `walk_measurable_loopFine/loopL`, as `Step2EventsGenTw_baGrid`).
### (iv) D2 texts, (viii) hypothesis table (the probe step compiles the D2 texts; none is a new named `Prop`)
| premise | band discharge | BA source / owner |
|---|---|---|
| `StepDecompGen_LoopForm Cm E` (`StepDecompGen:60`), targets 3, 4, 7-10 | `stepDecompGen_loopForm_band` :459 | definitional at `baStep2Mat` (`BA/Step2BA:54-72`; `Cm.m = BAmF`) + `0 < Im m`: T4-BA |
| `StepDecompGen_WalkForm Cm lam' Ψ` (:73), targets 7-10 (measurability of `Cm.Hpath`, `ZvecNg`) | `stepDecompGen_walkForm_band` :465 | definitional (`Step2BA:68-72`; lam′ = 0, Ψ = lam0 • PsiI): T4-BA / T5-BA |
| `Step2EventsGen_Law Cm μ Hf` (`Step2EventsGen:90`), target 4 | `Step2EventsGen_bandLaw` :1125 | `Step2EventsGenTw_baLaw` (`Step2EventsGenTw:64`, merged) |
| `Step34Gen_LCompat Cm Hf` (:164); `KCompat` is not expected to be read by target 4 (K enters as `Cm.K`; the 1b confirms) | `bandStep34_LCompat` | `Step34GenTw:85` shape: T4-BA |
| K1-K4 `GridRepTailGen_Ker C n` (`GridRepTailGen:54`, merged: import, never inline), targets 7, 8, 10 | `gridRepTailGen_ker_band` (`GridRepTailGen2:672`) | `gridRepTailGen_ker_BA` (`BA/GridRepTailBA:60`, merged) |
| `DecayGen_Spec`, `DecayGen_WardPair` (`DecayGen:91,96`) | `DecayGen_bandSpec` :142, `_bandWardPair` :160 | BA κ_m = κ (`DecayGenTw:72-77`), `DecayGenTw_baWardPair` |
| `STSEforLnConclgL` / `STSEforLngL`; `STEKDecaygL` | `bandFM_STSEforLn` + `stSEforLn_holds` (`SEforLn2:1287`); `bandFM_STEKDecay` + `stEtermDecay` (`DecayLoopB:2209`) | U2-BA (owed) |
| `STDecayLoopUgL` | `stDecayLoopUgL_of_step2` (`DecayGen:583`) from `STGdecayWgL` in `STStep2ConclgL` | T1 / T1-BA (registered) |
| `STKboundgL`, `STKwardgL` (inside `STIngRgL` :373) | K12 band | `baKbound_holds` (K12), BA-V |
| target 5: `GridDriftNg Cm s t K` (`HierDriftGen:630`), `HierDriftGen_KLink` :677, `Im m ≤ 1` | `gridDriftNg` :941, `hierDriftGen_kLink_band`, `hierDriftGen_band_eta` | T5-BA; `baStep2Mat_KI` (`Step2BA:89`); `BAm_norm_le_one` |
| target 9 (inline): `∀ ω, Cm.Hpath s t K n 0 ω ∈ GoodSetNg …` at `s n = 0` | `zero_mem_goodSetN_of_levels` (`AzumaProxyN:924`) | **none** (vi): owed to T4-BA |
D2 (3)-(5): the seven vocabulary items and `stepErrNg` are T2474's (`StepDecompGen:537-585`, `HierDriftGen:619`); bridges merged: `ZfamN ZvecN YvecN loopFamN stoppedEdgeN SubGaussStopN` proved (`pathH_succ`, `loopM_eq_loopL`, `bandStep2_Ugen`, :615-658), `SubGaussFormN` `Iff.rfl`, `stepErrN` `rfl` (`HierDriftGen:625`). `qvFormNg := (STeeUMg Cm n v w M σ a).re`: bridge **proved**, not `rfl`: `qvFormN` (`GridAssemblyN:105`) pairs `∏ uKer` with `conj ∏ uKer`, `STeeUMg` (`Step2Gen:983`) with `∏ uKer(!σ,!σ′)`; equal by K4 and `Step2Kern_uKer_band` (`Step2Gen:305`); the `conj` form is equivalent, `Re STeeUMg` is T8b's text. `GridAssemblyHypNg.hE : |E| ≤ 2` becomes the field `GridRepTailGen_Ker C n` (K2 gives the coarse bound `gridAsm_norm_Ugen_coarse`, :616). Targets 2-4 bridges: 2 `Iff.rfl`, 3 `Iff.rfl`, 4 through `bandFM_STIngR` (`Step34Gen:447`).
### (vi) Initial membership at BA: no source (not a RETURN, answer (5))
`grep -rlE "GoodSetN|GoodSetNg|zero_mem_goodSet" RBM3D | grep -v "^RBM3D/Induction/"` prints nothing (exit 1). Mathematics (reading, not Lean-checked): at BA `s n = 0`, `j = 0` gives `Hpath = lam0 • PsiI` (`seqHflow = √u X`, `Gauss/FineModel:225`; `Step2BA:68-72`), `G_0 = M^{(B)} ⊗ I` (`BAMfine`, `BA/FlowPins:255`); 𝒦 at u = 0 is the `M`-loop `BAMLoop` (paper `1_2:1000` `eq:initial_K`; `BA/KSolve:459` for lengths 2, 3, `KWard:299`), so the 𝓛−𝒦 clauses vanish; `M_aa = m` by translation invariance of Ψ_B and `(self_m)`, so `STavgErrM = 0`; left are the entry decay of M (`BA/CombesThomas`, `BAMB_ct_core`) and `(ℰ⊗ℰ)(H₀)` at levels (Γ, Λ) as `azumaProxy_hee_of_levels` (`AzumaProxyN:882`). Owed item for T4-BA; the U3s2/U3s3 consumers (ticket census: 6 + 8 uses of `zero_mem_goodSetN*`) need it at s = 0.
### (vii) UBA-C1: `sz.lam` / g′ / kernel reads (R1 not needed, no crossing)
| statements | `sz.lam` (size level) | g′ (walk coupling) | kernel |
|---|---|---|---|
| 1-4 | `ellT (sz.L n)(sz.lam n) u`, `sz.Bctl` | none (W not used; law = `Step2EventsGen_Law`) | none (`Cm.K`, `Cm.eta`) |
| 5 | none | none | none in the statement (`Cm.eta`, `GridDriftNg`) |
| 7 | none | only as the parameter of the premise W (not read) | `Step2Gen_UN Cm.toFlowFM`, K1-K4 |
| 8-10 | none | `gvarF d L W (lam′ n)` in `AzumaSubGNg`; `Cm.S n = SB d L (lam′ n)` in T2474's `qvPropagatedNg` | `Step2Gen_UN`, K2; `P ≤ N^{C_P}` independent of lam′ |
`lam′` is never compared with `sz.lam`; `grep -nE "withLam|BAflowLam0|gK"` on the new files must hit only inside W (acceptance).
### (ix) Premise scan, (x) `open private`, (xi) layout, (xii) size, (xiii) names
(ix) Expected `owedProps` lines (owner U2 / U2-BA, answer (8)): `STSEforLnConclgL`, `STEKDecaygL`, `STSEforLngL` (none is yet in `Test/Axioms.lean`; `STKcalDecaygL` is, :198). Concluded: `GoodExitMeasNg` etc. by the targets, `Step2EventsGen_Law`, `GridDriftNg`, `DecayGen_*`, `GridRepTailGen_Ker` by merged band theorems. Target 9 is an inline hypothesis, so no `Prop` and no registry line (owed item in (vi)). `grep -n STGridRepNgL` in the new files must print nothing (TN-C4).
(x) `open private … from`, 89 candidates (priv.py heuristic: private declarations whose body has none of the band tokens `zt etaT mE Ugen uKer pathH STLM STLIM … `; it also catches band-specific ones such as `gridGood_meas_STLKIM` :261, `_STXiLKM` :301, `_STavgErrM` :332, `goodExitMeasN_of_measurable` :416, `gridAsm_measurable_ZvecN_apply` :897, which the 1b copies instead, ≈ +100 lines, inside the (xii) uncertainty): GridGoodN:186,239,247,261,301,332,416,444,458,469,541,551,556,563,584,852,977,987; GridEnvelopeN:64,68,77,84,241,365,368,371,375,554,562; GridAssemblyN:266,271,276,280,291,296,300,309,461,465,661,708,758,777,797,812,876,897,988,993,998,1028,1054,1093,1144,1196; AzumaProxyN:98,124,138,146,156,187,191,222,945,949,957; AzumaProxyN2:90,98,107,141,160,172,180,200,209,227,253,266,274,282,297,307,389,405,618,622,830,837,863. Copy-adapt (band file:line, commit ab435c6e): `gridGood_whp_uniform` :677, `gridGood_grid` :879, `gridGoodN_holds` :930; `gridDriftN_envelope` :111; `gridAsm_core` :1378, `gridAsm_Ugen_four` :566, `stoppedAzumaZN` :1014, `assembledN` :1605, `gridAsm_stronglyMeasurable_ZvecN/YvecN` :927/:937; `azumaProxy_subG_ugen` :980, `_goodExit` :1010, `_pos_gridExitTauN` :1027, `_pathH_zero_of_s_zero` :970; `yMomentsUnifN` (`AzumaProxyN2:894-992`), `AzumaProxyN_stopW/YfieldsW` :1016/1025, `_pub` forms :1231-1258.
(xi) Imports: GridGoodGen `Chain/{GridDuhamelGen,Step34Gen,DecayGen,StepDecompGen,Step2EventsGen}`, `Induction/GridGoodN` (+`Step2EventsGen` is F2); GridEnvelopeGen `Chain/{HierDriftGen,DecayGen}`, `Induction/GridEnvelopeN` (+`HierDriftGen`: it reads T2474's `stepErrNg`, `gridDriftNg`); GridAssemblyGen `Chain/{GridDuhamelGen,StepDecompGen,GridRepTailGen}`, `Induction/GridAssemblyN`; AzumaProxyGen `GridGoodGen`, `GridAssemblyGen`, `Induction/AzumaProxyN2`. No `BA/*` import; new files have no outside importer (44-module cone untouched). Status: T2471 merged (both halves), T2467 merged, T2474 merged (state files).
(xii) `cd $S/T2473 && python3 -I d3.py` (T2474 method, `T2474-prove.md:68`: band spans × 0.88 + itemised new material + flat instances; model-free privates cost 0). Output verbatim:
```
GridGoodGen      port  846 x0.88= 744 +new 160 +inst 120 +hdr 45 = 1069
GridEnvelopeGen  port  105 x0.88=  92 +new 120 +inst  60 +hdr 45 = 317
GridAssemblyGen  port  995 x0.88= 876 +new 140 +inst 150 +hdr 45 = 1211
AzumaProxyGen    port 1099 x0.88= 967 +new 270 +inst 150 +hdr 45 = 1432
T4s2a (GridGood+Envelope) 1386 | GridAssembly 1211 | AzumaProxy 1432 | two-row T4s2b 2643
own central 4029; ticket central 2900 (ratio 1.39); T2474 ticket 1900 -> landed 2627 (ratio 1.38); 2900*1.38=4010; REQ line 3900; max file 1432 < stop 2000
```
**F1:** the pre-signed split fires, but its second half (GridAssemblyGen + AzumaProxyGen = 2,643) exceeds 1,950, and own central (4,029) is above the 3,900 REQ line (the ticket's central 2,900 is below it; T4s2a = 1,386 is fine): the dispatcher decides at the 1a-audit between a third row (GridAssemblyGen | AzumaProxyGen, stacked A → B → C; short REQ) and a re-estimate; no file nears 2,000 and no reserve file is needed.
(xiii) `clash.sh | awk 'NR==1{print;next}{n[$NF]++} END{for(k in n) print n[k]" refs -> "k}'` (`git grep -w` of 48 names: every new public name and the four stems) prints `refs: HEAD t/T2465 t/T2469 t/T2470 t/T2471 t/T2471b t/T2472 t/T2467 t/T2474` and `9 refs -> none`. `t/T2472b`, `t/T2478`, `t/T2479` do not exist yet; tickets T2475-T2479 mention the four stems only in their sibling scans (`grep -w`).
### Verdicts
Target 1 PASS; 2 PASS (clauses equal `GoodSetN`'s, `T2473_GoodSetNg` consistent); 3 PASS (measurability from LoopForm); 4 (a) and (b) PASS (law, LCompat and LoopForm give the single-time to grid transfer; (b) takes B ≤ 1 and the window from `STConStInd` as `GridGoodN:928-952`, and needs `Step2EventsGen_Flow` for admissibility and T0 < 1); 5 PASS (F3); 6 dropped; 7 PASS; 8 PASS; 9 PASS with owed BA item; 10 PASS; 11 PASS; 12 PASS. Stop rules checked: no pin fails, no new `FlowFM`/`Step2Mat` field, no third kernel, no `BA/*` import, no band edit, no (B) row without a field except the dispatcher-resolved initial membership. **Overall verdict: PASS.**
### Fill-in table (CONTROL H250 (4))
| # | deliverable | line / n/a |
|---|---|---|
| (i) | exponent table | L5-18 (C_K, C_P, D₁, τ_K, RangeCond, `(1+(1-u)^{-1})^k`, Γ) |
| (ii) | instance, n = 0, 1, 10, band and BA | L19-40 |
| (iii) | D1 census and route | L41-44; route (a), no switch |
| (iv) | D2 texts, band discharge, BA source | L45-59; compiled by the probe step after this section (n/a here: no Lean at 1a) |
| (v) | vocabulary, `stepErrNg`, `qvFormNg`, bridge kind | L59 |
| (vi) | initial membership at BA | L60-61: no source, owed to T4-BA, not a RETURN |
| (vii) | UBA-C1 table | L62-69: no crossing |
| (viii) | hypothesis table | L46-58 |
| (ix) | premise-scan preview, registry | L71 |
| (x) | `open private` list, copies | L72 |
| (xi) | layout | L73 |
| (xii) | lines per file, split | L74-83 (F1) |
| (xiii) | name-clash grep | L84 |

## (a″) Probe compile — Mon Oct 12 23:11:29 UTC 2026
Probe step of the ticket (role prover-hard). The pre-signed switch to `prover-max` is not fired: (a) Decisions (1) picks route (a) for every layer; the only declarations without a field are the initial membership, which is target 9's inline hypothesis by dispatcher answer (5) and not a route-(b) layer. Files written: `RBM3D/Probe/T2473Pins.lean` (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2473`, branch `t/T2473`, commit `b8c9b113`, never merged, no root import) and this section; section (a) is untouched.
```
$ date -u; lake env lean RBM3D/Probe/T2473Pins.lean; echo "exit=$?"; date -u
Mon Oct 12 23:10:12 UTC 2026
exit=0
Mon Oct 12 23:10:18 UTC 2026
$ wc -l RBM3D/Probe/T2473Pins.lean
     400 RBM3D/Probe/T2473Pins.lean
$ grep -nE "sorry|admit|native_decide|^axiom|STGridRepNgL|def .*[Kk]er|def Ugen" RBM3D/Probe/T2473Pins.lean; echo "grep-exit=$?"
grep-exit=1
$ grep -n "^import RBM3D.BA" RBM3D/Probe/T2473Pins.lean
6:import RBM3D.BA.Step2BA
$ git log --oneline -1; git status --short
b8c9b113 T2473 probe: D2 texts of T4s2 compiled against main 
```
The compile output is empty (no error, no warning). The one BA import is the probe's (BA readings, lines 390-395); the final `Chain` files import none. Axioms: scratch copy of the final probe (script `mkax.py` in the scratchpad `T2473/`: every `example` renamed `exN`, one `#print axioms` per named declaration):
```
$ lake env lean pins_ax.lean | sed -E "s/^'[^']*' //" | sort | uniq -c        (exit 0)
     42 depends on axioms: [propext, Classical.choice, Quot.sound]
```
(28 named declarations of the probe and `ex1`..`ex14`; `structure GridAssemblyHypNg`, the `instance` and the `private` items are not printed.) Name clash at probe time (`clash.sh`, `git grep -w` of 48 names): `none` on `HEAD` and on `t/T2465 t/T2469 t/T2470 t/T2471 t/T2471b t/T2472 t/T2467 t/T2474`; `t/T2478`, `t/T2479` do not exist.
### Probe map (D2 texts compiled; line numbers of `RBM3D/Probe/T2473Pins.lean`)
| D2 item | text (lines) | band discharge, `bandStep2Mat sz0 (STflowE z0)` (lines) | BA reading |
|---|---|---|---|
| W `StepDecompGen_WalkForm Cm lam' Ψ` (T2474, merged) | merged | `stepDecompGen_walkForm_band` (348) | definitional: `baStep2Mat_walkForm` (329-332), instance at `sz0` (390-392): `lam' = 0`, `Ψ = lam0 • PsiI`, Hermitian by `PsiI_isHermitian` |
| LoopForm (`LM`, `LIM`, `eta` compat) | merged | `stepDecompGen_loopForm_band` (347) | definitional except `0 < Im (BAmF …)`: `baStep2Mat_loopForm` (333-335), T4-BA |
| measurability of `Cm.LM`, `Cm.LIM` in `H` | `T2473_meas_of_loopForm` (319-328) | follows from LoopForm; no separate compat `Prop` | same |
| S: `HermTestFunLoopNOf`; `QVPropagatedNg` | merged | 349; `qvPropagatedNg … fun _ => rfl` (350) | `hS : Cm.S n = SB …`: T4-BA / T5-BA (not compiled) |
| K1-K4 `GridRepTailGen_Ker` (T2471, imported) | merged | `gridRepTailGen_ker_band` (351) | merged `gridRepTailGen_ker_BA` (`BA/GridRepTailBA:60`); not compiled here |
| `Step34Gen_LCompat`; `Step2EventsGen_Law` (F2) | merged | 352; 353 | `Step2EventsGenTw_baLaw` (merged); LCompat: T4-BA |
| `DecayGen_Spec` | merged | `DecayGen_bandSpec` (354) | BA `κm = κ` (`DecayGenTw:72-77`) |
| target 2 `GoodSetNg`; target 3 `gridExitTauNg`, `goodExitTauNg`, `GoodExitMeasNg` | 31-68 | `Iff.rfl` / `rfl` (99-108) | check-file shapes (not re-compiled) |
| target 4 `GridGoodNConclg`, `GridGoodNgL` | 69-93 (= `T2473_GridGoodNConclg`, `T2473_GridGoodNgL`) | `bandStep2_GridGoodNConcl` `Iff.rfl` (107-108); `bandStep2_GridGoodN` through `bandFM_STIngR` (109-113) | `GridGoodNgL 3 … baStep2Mat … BAflowT0` typechecks (394) |
| target 4 (a) statement `T2473_gridGoodNConclg_of_stmt` | 291-305 | premises discharged one by one (347-354) | — |
| target 5 `T2473_gridDriftNg_envelope_stmt`, `T2473_sum_gridStep_div_etaNg_le_stmt`, `SumWeightedStepErrNg_Stmt` | 254-285 | `GridDriftNg` at band (355-359); `SizeTendsto`, link, `Im m ≤ 1`, `0 < η ≤ 1 - v` (360-367); `STKboundgL` stays external | T5-BA |
| target 9 `T2473_InitMem` | 286-289 | from `zero_mem_goodSetN_of_levels` (373-380) | **no source** ((a) (vi)); owed to T4-BA |
| `qvFormNg := (STeeUMg …).re` | 121-124 | **proved**, not `rfl`: `bandStep2_qvFormN` (312-318), hypotheses `|E n| ≤ 2`, `|w| < 1` | — |
| target 7 `StoppedAzumaZNg`, `AssembledNg`, `GridAssemblyHypNg` (`hKer` for `hE`), `YMomentBoundsNg`, `YMomentsConclNg`, `YMomentsNg` | 125-247 | `StoppedAzumaZNg` from `stoppedAzumaZN` (381-389) | `AssembledNg (baStep2Mat …)` typechecks (394-395) |
| target 8 `AzumaSubGNg Cm g` | 136-150 | from `azumaSubGN` through `bandStep2_ZfamN` (368-372) | `AzumaSubGNg (baStep2Mat …) 0 …` typechecks (395) |
| target 10 `YMomentsUnifNg` | 176-184 | — | — |
### Findings of the probe (none changes a verdict of (a))
1. **Imports (correction of (a) (xi)).** The band discharge of K, `gridRepTailGen_ker_band`, is in `Chain/GridRepTailGen2` (imports `Chain/GridRepTailGen` only), not in `GridRepTailGen`: `GridAssemblyGen` and `AzumaProxyGen` need `import RBM3D.Chain.GridRepTailGen2` for their band corollaries. `GridGoodGen` needs `Chain/Step2EventsGen` (the probe compiles with it; `Step2EventsGenTw` is not needed).
2. **Instance binder.** `StoppedAzumaZNg`, `AzumaSubGNg`, `AssembledNg` carry `[IsProbabilityMeasure Cm.Pp]` (read by `SubGaussFormNg`). Band: merged `bandStep2Mat_isProbabilityMeasure_Pp`. BA: the instance is written in the probe (393, one line, `isProbabilityMeasure_pathP (sz.withLam 0)`) and belongs to T4-BA. For the 1a-audit: keep the binder, or derive it from W inside the theorems.
3. **Premises that left the texts.** `YMomentsNg`, `YMomentsUnifNg`: `0 < κ` and `|E n| ≤ 2 - κ` become `DecayGen_Spec Cm.toFlowFM κm` (so `0 < κm ≤ Im m`). `StoppedAzumaZNg`: `∀ n, |E n| < 2` is dropped (the band corollary supplies it, 382). `AzumaSubGNg`: the walk coupling is the explicit argument `g` (band `sz.lam`, BA `0`); `Ψ` occurs only in W of the theorem.
4. **Target 4 (a)** is compiled with LoopForm + `Step2EventsGen_Law` + `Step34Gen_LCompat` (F2 of (a)); no `KCompat`, no W. Target 4 (b) (family form) is not compiled in the probe (400-line limit); its text is the check file's, with the same replacement.
5. **Not compiled (1b, target 11):** the conversion `GridAssemblyHypN → GridAssemblyHypNg` at the band, concrete-data instances of `GridAssemblyHypNg`, `AssembledNg`, `YMomentsNg`, the BA discharges.
6. **Greps on the probe.** Hypothesis-rule pattern of the ticket, hit lines `17 111 112 125 171 185 186 269 312 313 318 325 339 343 344 346 347 352 353 366 371 378 379 381 382 388 393`: docstrings (17, 125, 171, 185-186, 269, 312, 339), band bridge (111-112), `bandStep2_qvFormN` (313, 318), `T2473_meas_of_loopForm` (325), the `sz0`/`z0` instance section (343-388), BA instance (393); none in a generic text. UBA-C1 pattern `withLam|BAflowLam0|gK`: lines `137 393 394` (docstring, BA instance, BA reading of the pin family; no generic text, no crossing of `sz.lam` with a kernel or a coupling). U-C4 `def .*[Kk]er|def Ugen`: 0 hits; `GridRepTailGen_Ker` is imported (the field `hKer`, one example), no second named `Prop`.
### Fill-in table (CONTROL H250 (4)) after the probe step: every row filled
| # | status | where |
|---|---|---|
| (i)-(iii) | filled in (a) | (a) L5-44 |
| (iv) | **filled**: D2 texts compiled, exit 0; band discharge and BA source per field | probe map above |
| (v) | **filled**: `ZfamN`, `ZvecN`, `YvecN`, `loopFamN`, `stoppedEdgeN`, `SubGaussStopN` proved bridges, `SubGaussFormN` `Iff.rfl`, `stepErrN` `rfl` (T2474, merged); `qvFormNg` proved (312-318); `GoodSetNg`, `GoodExitMeasNg`, `GridGoodNConclg` `Iff.rfl`; `GridGoodNgL` through `bandFM_STIngR` | (a) L59; lines 99-113, 312-318 |
| (vi) | filled in (a): no BA source, owed to T4-BA (dispatcher answer (5)) | (a) L60-61 |
| (vii)-(ix) | filled in (a) | (a) L62-71 |
| (x) | filled in (a) | (a) L72 |
| (xi) | filled in (a), corrected by finding 1 | (a) L73 |
| (xii) | filled in (a): F1, own central 4,029 above the 3,900 REQ line | (a) L74-83 |
| (xiii) | filled in (a), re-run at probe time: `none` on `main` and 8 sibling branches | above |

## (a‴) Sign-off answers (H262, Amend 1) — Mon Oct 12 23:53:06 UTC 2026
Binding: `docs/tickets/T2473-amend-1.md` (dispatcher V3, 23:28 UTC; CONTROL H262 (2)). Section (a) and (a″) are untouched; no correction of (a) is needed: each answer below resolves a flag of (a) (F1, F3, F2) and agrees with its numbers. Mathematics only; no Lean written. Scratch: `T2473/rows3.py` in the session scratchpad.
### S1 — three rows (answer to F1); D3 table per row, from the inputs of (a) (xii) L76-79
```
$ python3 -I $S/T2473/rows3.py
T4s2a ['GridGoodGen', 'GridEnvelopeGen'] 1386 max file 1069 <= stop 2000: True <= 1950 pre-sign: True
T4s2b ['GridAssemblyGen'] 1211 max file 1211 <= stop 2000: True <= 1950 pre-sign: True
T4s2c ['AzumaProxyGen'] 1432 max file 1432 <= stop 2000: True <= 1950 pre-sign: True
total 4029 REQ line 3900 exceeded: True -> third row, short REQ (non-blocking)
```
| row | files (targets) | own central | largest file | boundary |
|---|---|---|---|---|
| T4s2a (this run) | `Chain/GridGoodGen` 1,069 + `Chain/GridEnvelopeGen` 317 (1-5) | 1,386 | 1,069 | imports of (a) (xi) with the probe correction (a″) finding 1; branch `t/T2473`, merges first |
| T4s2b | `Chain/GridAssemblyGen` 1,211 (7; 6 dropped) | 1,211 | 1,211 | stacked on `t/T2473` after T4s2a audit PASS; needs `Chain/GridRepTailGen2` (a″ finding 1) |
| T4s2c | `Chain/AzumaProxyGen` 1,432 (8-10) | 1,432 | 1,432 | stacked after T4s2b; imports `GridGoodGen`, `GridAssemblyGen`; reserve `AzumaProxyGen2` only if predicted above 1,800 (1,432 is below) |
Each row is below the pre-signed 1,950 and every file below the stop line 2,000; the sum 4,029 is the (a) F1 figure, above the 3,900 REQ line, hence the third row and a non-blocking notice REQ. Row sums equal (a) L80 (1,386 / 1,211 / 1,432). Exponent table (i) and instance (ii) of (a) are unchanged by the split (the rows (i) list no file-dependent constant).
### S2 — target 5 premise list (answer to F3)
```
$ grep -n "(Cm.m n).im ≤ 1\|def SumWeightedStepErrNg_Stmt\|def T2473_gridDriftNg_envelope_stmt\|def T2473_sum_gridStep" RBM3D/Probe/T2473Pins.lean   # worktree t/T2473, commit b8c9b113
256:def T2473_gridDriftNg_envelope_stmt (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] : Prop :=
270:def T2473_sum_gridStep_div_etaNg_le_stmt (Cm : Step2Mat sz) : Prop :=
276:def SumWeightedStepErrNg_Stmt : Prop :=
278:    DecayGen_Spec Cm.toFlowFM κm → (∀ n, (Cm.m n).im ≤ 1) → 0 < τ' → τ' ≤ 1 → 0 < τK → 0 ≤ D_t → 2 ≤ k →
```
Admitted: the inline premise `∀ n, (Cm.m n).im ≤ 1`, next to `∀ n v, 0 ≤ v → v < 1 → 0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v` (`hη` of `exists_norm_KI_le_wing`, `HierDriftGen:1083`). No named `Prop`, no registry line. Premise list of target 5 after S2 (probe texts, lines 254-285):
| statement | premises beyond the pins | `Im m ≤ 1` |
|---|---|---|
| `gridDriftNg_envelope` (256) | 2 ≤ k, τK > 0, SizeTendsto, `STKboundgL`, link `KI = K`, hη, 0 ≤ s ≤ t < 1, K ≠ 0, `GridDriftNg Cm s t K` | via hη (`η ≤ 1 - v`); the probe text carries hη, not the separate line; the 1b adds the line of 278 if its proof reads `Cm.m` |
| `sum_gridStep_div_etaNg_le` (270) | `DecayGen_Spec` κm, τ' > 0, ranges, `RangeCond τ' t` | not read (κm ≤ Im m only) |
| `SumWeightedStepErrNg_Stmt` (276) | `DecayGen_Spec`, **`Im m ≤ 1` (278)**, 0 < τ' ≤ 1, τK > 0, D_t ≥ 0, 2 ≤ k, SizeTendsto, ranges, RangeCond, the four C_K inequalities of (a) (i) row C_K, `N^{C_K} ≤ K` eventually | inline premise (E′ reduction, (a) L18: `E′ = 2√(1-(Im m)²)` is real only if `Im m ≤ 1`) |
Discharges. Band: `hierDriftGen_band_eta` (`HierDriftGen:1250`; `|E n| ≤ 2 − κ`, probe 360-367 derives `Im m ≤ 1` from its `v = 0` case). BA: owed to T4-BA via `BAm_norm_le_one` (`BA/Ward`, used as `Im m ≤ ‖m‖ ≤ 1` at `BA/EMn2BA:98-103`) with its side conditions. Slack at the instance of (a) L25-26: `1 − Im m` = 0.032 (band, `Im m` = 0.9682) and 0.1675 (BA n = 0, `Im m` = 0.83249), positive at n = 0, 1, 10; the exponent table (i) is unchanged (the premise enters no exponent).
### S3 — target 4 reads (answer to F2)
| read | text | where | used by |
|---|---|---|---|
| `StepDecompGen_LoopForm Cm E` | `StepDecompGen:60` (T2474, merged) | band `stepDecompGen_loopForm_band` :459; BA `baStep2Mat_loopForm` up to `0 < Im m` (T4-BA) | targets 3, 4 (a)/(b); gives `Cm.LM = loopFine`, `Cm.LIM`, `Cm.eta = etaOf`, measurability of `LM`, `LIM` in `H` (probe `T2473_meas_of_loopForm` 319-328) |
| `Step2EventsGen_Law Cm μ Hf` | `Step2EventsGen:~88` (T2467, merged; last conjunct of F9) | band `Step2EventsGen_bandLaw` :1125; BA `Step2EventsGenTw_baLaw` (merged) | target 4 (a) (probe 291-305, compiled); (b) the same replacement (probe does not compile (b), (a″) finding 4) |
Replaced in target 4: `StepDecompGen_WalkForm`, `Step34Gen_KCompat` and the measurability compat (Amend S3). Kept: `Step34Gen_LCompat Cm Hf` (probe 295; Amend S3 does not name it, so it stays, and (a) viii row 4 lists it), `DecayGen_Spec`, `Admissible`, `B ≤ 1` on the window, the `STSEforLnConclgL`, `STDecayLoopUgL` and four `STEKDecaygL` premises. W is read only at targets 7-10 (T4s2b, T4s2c), not in this run. The unproved BA items stay as in (a) viii: LoopForm up to `0 < Im m`, LCompat, `Step2EventsGenTw_baLaw` (merged); the BA initial membership (target 9) is still the owed T4-BA item ((a) vi, Amend 4).
### Verdict of (a‴)
Consistent with (a): numbers of (xii) reproduced (rows 1,386 / 1,211 / 1,432), `Im m ≤ 1` holds at the instance of (ii), and the S3 reads are those of the probe (a″) and of F2. Targets 1-5 (this run, T4s2a) **PASS**; 7-10 are T4s2b and T4s2c and keep their (a) verdicts. **Overall verdict: PASS.**

## (a′) Preflight corrections — Tue Oct 13 00:30:29 UTC 2026
Stage 1b of T4s2a (Amend 1). One mistake of (a″) finding 4 / (a‴) S3 changes a verdict: **target 4 (a)/(b): PASS → BLOCKED**. `GridGoodNConclg` ends in `GoodSetNg … (Cm.Hpath …)`, whose first clause is `H.IsHermitian`. The S3 premises (`StepDecompGen_LoopForm`, `Step2EventsGen_Law`, `Step34Gen_LCompat`, `DecayGen_Spec`, `Admissible`, the ≺ inputs) never state it; the dropped W (`hW.1`, `pathH_isHermitian`) was its only source. Script (`herm.py`, count of `Hermitian` in each definition): `LoopForm=0 WalkForm=1 Law=0 LCompat=0 DecayGen_Spec=0 WardPair=0 STKcalDecaygL=0 STDecayLoopUgL=0 STSEforLnConclgL=0 STEKDecayKgL=0 Admissible=0`. A negative statement is not compiled (a counter-model needs a `Step2Mat` with non-Hermitian grid states that meets every ≺ premise: infeasible here). Stop rule "a target needs a premise outside the list": no public `gridGoodNConclg_of` / `gridGoodNgL_of` is stated, no hypothesis was added. **Required from the dispatcher (one of):** (i) add `StepDecompGen_WalkForm Cm lam' Ψ` (T2474's text, already a premise of target 3's `goodExitMeasNg`; band `stepDecompGen_walkForm_band`, BA `baStep2Mat_walkForm`) to (a) and (b); (ii) add `∀ n u ω, (Hf n u ω).IsHermitian`. Both options compile in the scratch file `$S/t4_public_with_W_or_H.lean` (`$S` as in (b); = the committed `GridGoodGen.lean` + `gridGoodNConclg_of_scratch`, `gridGoodNgL_of_scratch` with (i), `gridGoodNConclg_of_scratch_ii` with (ii) for (a); exit 0, `#print axioms` of the three: the standard three). The committed file already holds their private core `GridGoodGen_whp_uniform`, `GridGoodGen_grid` (Hermiticity enters only the last step, as the `Cm.Pp`-a.s. premise `hHerm`).

### (a′) addendum — Tue Oct 13 01:24:27 UTC 2026
Resolved by Amend 2 (dispatcher V3, Tue Oct 13 00:46 UTC 2026, `docs/tickets/T2473-amend-2.md`, option (i)): target 4 (a) and (b) PASS again. `StepDecompGen_WalkForm Cm lam' Ψ` is the premise `hW`; the proofs read it only for the Hermitian clause (`hW.1`, `StepDecompGen_Hpath_eq`, `pathH_isHermitian`). No Hermitian `Hf` premise (option (ii)) is used.

## (b) Script output (stage 1b of T4s2a resumed under Amend 2, branch `t/T2473`; scripts in the session scratchpad `T2473/`)
Resume: `date -u` Tue Oct 13 00:55:59 UTC 2026 at db4066bc (targets 1, 2, 3, 5 as committed). Commits since: fcc3e82b (public target 4, band instances), 7d9872c6 (merge of `main` 16861112, for `Test/Axioms.lean`), 21dafaa9 (registry lines), 9bb7bae1 (instances), de1b76b7 (docstrings). Stop rule: 1,037 and 360 lines against 2,000 per file, no stop.
```
$ date -u; git log --oneline -1; wc -l RBM3D/Chain/{GridGoodGen,GridEnvelopeGen}.lean      (stop size 2,000 per file)
Tue Oct 13 01:22:39 UTC 2026
de1b76b7 T2473: GridGoodGen header docstrings after Amend 2
    1037 RBM3D/Chain/GridGoodGen.lean
     360 RBM3D/Chain/GridEnvelopeGen.lean
$ lake build RBM3D.Chain.GridGoodGen RBM3D.Chain.GridEnvelopeGen 2>&1 | grep -E "Build completed|error"
Build completed successfully (3836 jobs).
$ lake build RBM3D   (01:05 UTC, after the merge of main; RBM3D.lean does not import the two modules)
Build completed successfully (4325 jobs).
$ lake env lean axioms_mine.lean      (#print axioms, the 44 public declarations of the two files)
  44 depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean inst4_ax.lean      (scratch copy: the two target-4 examples renamed inst4_1, inst4_2)
   2 depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean root_check.lean      (RBM3D.lean + the two import lines + #assert_rbm_axioms; registry: owed premises, theorems assuming each)
axiom audit: 14273 theorems, 4509 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.STSEforLnConclgL: 2 [no certificate]
  RBM.BA.STSEforLngL: 2 [no certificate]
  RBM.BA.STEKDecaygL: 3 [no certificate]
$ python3 t4stmt.py      (binders and conclusion of the target-4 theorems, extracted from the file)
theorem gridGoodNConclg_of  [21 binders]
  binders: Cm | E | μ | Hf | lam' | Ψ | κm 𝔠 𝔡 | s t | hL | hW | hLaw | hC | hspec | hA | hs0 | hst | ht1 | hB1 | hSE | hU | hEK
  conclusion: GridGoodNConclg Cm μ s t
theorem gridGoodNgL_of  [19 binders]
  binders: d | law | Flow | mkM | T0 | Hf | E | lam' | Ψ | hSE | hFlow | hSpec | hL | hW | hLaw | hC | hWard | hKcal | hEK
  conclusion: GridGoodNgL d law Flow mkM T0
$ python3 t4diff.py      (against the probe text T2473_gridGoodNConclg_of_stmt, b8c9b113)
premises (hypotheses after the binders): probe 12 (plus `∀ {d : ℕ}, 3 ≤ d`), mine 13; identical in both: 12
  MINE ONLY hW : StepDecompGen_WalkForm Cm lam' Ψ
$ python3 pindiff2.py; iffrfl.lean; thmstmts.lean      (identical-def count vs the 1a-audit probe texts; error-line counts of the Iff.rfl examples and the target-5 statement derivations)
7
0
0
$ clash2.sh: git grep -w of the 44 public names on main and every t/T245x-t/T248x branch except t/T2473
39 refs -> none
$ grep -nE "def .*[Kk]er|def Ugen" | grep -n STGridRepNgL | grep -n "^import RBM3D.BA" | grep -nE "sorry|admit|native_decide|^axiom"      (both files)
(no hit)
$ grep -nE "withLam|BAflowLam0|gK" (both files)
RBM3D/Chain/GridGoodGen.lean:233:  exact hT.comp (pathH_measurable_filt (sz.withLam lam') s v K n j)
RBM3D/Chain/GridGoodGen.lean:797:gives the Hermitian clause of `GoodSetNg`, `Cm.Hpath = Ψ + pathH (sz.withLam 
RBM3D/Chain/GridGoodGen.lean:832:      exact (hW.1 n).add (pathH_isHermitian (sz.withLam lam') s v K n j ω)) h
RBM3D/Chain/GridGoodGen.lean:896:        (pathH_isHermitian (sz.withLam (lam' sz z)) s v K n j ω)) hU'
$ git diff db4066bc HEAD -- (the two files) | grep -c "^[+-].*open private"; git diff main...t/T2473 --name-only; (Induction Path BA Chain/{Carrier,Step2Gen,Step2Kern,GridDuhamelGen,DecayGen,Step34Gen} RBM3D.lean) | wc -l
0
RBM3D/Chain/GridEnvelopeGen.lean RBM3D/Chain/GridGoodGen.lean RBM3D/Probe/T2473Pins.lean RBM3D/Test/Axioms.lean 
       0
$ python3 x1c1.py      (hypothesis-rule grep of the ticket; hit lines classified; none in a generic statement text)
GridGoodGen.lean: docstring L36,64,69,94,115,143,223,448,797,903,929,939,995,1012,1014; LoopForm unfolding (proof) L91,346; W (walk fact) L230,233,832,896; band bridge L489,490; band instance L917,932,933,934,935,936,941,942,996,997,1002,1005,1016,1017,1018,1019
GridEnvelopeGen.lean: docstring L21,27,135,216; E' reduction (proof) L207,218,252,254,256,257; band instance L293
$ git diff db4066bc HEAD --stat -- the two files; grep -nE "InitMem|zero_mem_goodSet" (both files)      (only GridGoodGen changed since the resume point, its 10 deleted lines are docstrings and the `open` line; no initial membership: supervisor 2351 T4S2-C2/C3)
 RBM3D/Chain/GridGoodGen.lean | 179 ++++++++++++++++++++++++++++++++++++++++---
 1 file changed, 169 insertions(+), 10 deletions(-)
(no hit)
$ grep -nE "^example \(hSE|^example : GridGoodNgL|gridGoodNConclg_of Cm1|gridGoodNgL_of 3" RBM3D/Chain/GridGoodGen.lean      (the two compiled target-4 instances)
1002:example (hSE : STSEforLnConclgL Cm1 (seqHflow sz0) (Sizes.seqP sz0) sInst tInst)
1005:  have h := gridGoodNConclg_of Cm1 E1 (Sizes.seqP sz0) (seqHflow sz0) sz0.lam (fun _ => 0) (Real.sqrt 1 / 2) (1 / 6) (1 / 10)
1016:example : GridGoodNgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
1018:  have h := gridGoodNgL_of 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
```
Narrative. (1) `gridGoodNConclg_of` (GridGoodGen.lean:808) and `gridGoodNgL_of` (:839) apply the private core `GridGoodGen_whp_uniform` (:543, port of band `gridGood_whp_uniform`, `GridGoodN:677`) and `GridGoodGen_grid` (:727, port of `gridGood_grid`, `:879`); the Hermitian clause of `GoodSetNg` is `hW.1 n` plus `pathH_isHermitian (sz.withLam lam')` (`lam'`, `Ψ` occur only in `hW`; the UBA-C1 grep hits are the W-using proofs at :233, :832, :896 and one docstring at :797).
(2) Against the probe text `T2473_gridGoodNConclg_of_stmt`: one premise added, `hW` (Amend 2), and `3 ≤ d` dropped (the proof does not read it; the Eterm decays and `STDecayLoopUgL` are premises). (b) is the family form: premises `STSEforLngL`, `Step2EventsGen_Flow`, a spectral `∃ κm`, `LoopForm`/`WalkForm` per flow, `Law`/`LCompat` per carrier, `DecayGen_WardPair`, `STKcalDecaygL`, the Eterm family; `STDecayLoopUgL` (from `stDecayLoopUgL_of_step2` and the `STGdecayWgL` in `STStep2ConclgL`) and `B ≤ 1` (from `STConStInd`, as `GridGoodN:928-952`) are derived, `3 ≤ d` comes from the pin.
(3) Instances (`GridGoodGenCheck`, `d = 3`, `sz0`; n = 0 has L = 4, W = 32, N = 2097152): (a) at `Cm1 = bandStep2Mat sz0 E1`, `E1 ≡ 1/2`, `κ = 1`, `κm = 1/2`, `𝔠 = 1/6`, `𝔡 = 1/10`, `s ≡ 0`, `t ≡ 1/16` applies `gridGoodNConclg_of` with `LoopForm`, `WalkForm` (`sz0.lam`, `Ψ = 0`), the law, `LCompat`, `DecayGen_Spec`, `Admissible`, `B ≤ 1` (from `Bctl_tInst_tendsto`) and the Eterm decays (`stEtermDecay` from the loop decay) discharged; open: `STSEforLnConclgL`, `STDecayLoopUgL` (U2, T1 pins); it concludes `GridGoodNConclg` and, by `bandStep2_GridGoodNConcl`, the band `GridGoodNConcl sz0 E1 sInst tInst`. (b) applies `gridGoodNgL_of` over the band family with no open hypothesis (`STSEforLngL` is `stSEforLn_holds 3`, `STKcalDecaygL` is `bandFM_STKcalDecay`) and concludes `GridGoodNgL …` and `GridGoodN 3`. Targets 1-3, 5 and their instances are as committed at db4066bc.
(4) Registry: the root check passes with 3 `owedProps` lines (`STSEforLnConclgL`, `STSEforLngL`, `STEKDecaygL`, owner U2 / U2-BA, answer (8)) and one `structuralProps` line (`RBM.Gauss.Sizes.STAny`, `fun _ _ _ => True`, reported by the scan as an argument of `STSEforLngL`).

## (c) Verified Mathlib names (all used in the two files, compiled)
`Finset.sup'_apply`, `Finset.measurable_sup'`, `Measurable.of_eval_matrix`, `isClosed_eq`, `Continuous.matrix_conjTranspose`, `Set.ofPred_and`, `Real.sqrt_sq`, `Real.sq_sqrt`, `Real.one_sub_inv_le_log_of_pos`, `Real.log_div`, `Finset.sum_range_sub'`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `ae_all_iff`, `ae_iff`, `measure_mono`, `Set.mem_iInter`, `Finset.sum_le_card_nsmul`, `Nat.card_Icc`, `gt_mem_nhds`, `Filter.Tendsto.eventually`, `Filter.Eventually.of_forall`. Verified absent or deprecated: `push_neg` (deprecated warning in this Mathlib; replaced by `rw [not_le]`).

## (d) Open issues and paper-delta candidates
- Delivered: targets 1-5 of T4s2a. T4s2b (target 7) and T4s2c (targets 8-10) are not in this run. Next: the one audit of T4s2a as delivered (Amend 2 item 3); the last script block above is the evidence for supervisor 2351 T4S2-C2/C3 (no initial membership, no new `open private`).
- For the hub: `main` is merged into `t/T2473`, so the branch copy of `Test/Axioms.lean` is main's plus 5 lines; `RBM3D.lean` is not edited here, the hub adds `import RBM3D.Chain.GridGoodGen` and `import RBM3D.Chain.GridEnvelopeGen` at merge. `RBM3D/Probe/T2473Pins.lean` stays on the branch, never merged.
- Flag for the dispatcher: the ticket expected three registry lines; the scan also reports `STAny`, registered as structural (a regime selector, not a result). Confirm the class.
- BA owed items unchanged: initial membership (target 9, T4-BA), `0 < Im m` of `baStep2Mat_loopForm`, `BAm_norm_le_one` for target 5, BA discharge of `hSE`, `hU`, `hEK` (U2-BA, T1-BA).
- Paper-delta candidates: **T2473a** the `_Hf` lemmas of target 1 carry the LM compat as an inline premise (`GridGoodGen_LM_eq_L` derives it from `LoopForm` and `Step34Gen_LCompat`); **T2473b** target 5 `sum_weighted_stepErrNg_le` has the allowed premise `∀ n, (Cm.m n).im ≤ 1` (band: derived from `|E| ≤ 2 - κ`; BA: `BAm_norm_le_one`, T4-BA); **T2473c** the Hermitian clause of target 4 is read from `StepDecompGen_WalkForm` (Amend 2); **T2473d** `GoodExitMeasNg` is stated through `goodExitTauNg`, equal to `T2473_GoodExitMeasNg` by `Iff.rfl`; **T2473e** target 4 (a) drops the unused `3 ≤ d` of the probe text.
