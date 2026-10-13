Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 06:47:23 UTC 2026

Scratch (Python only, no Lean): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2493` (`$S/{closure,duhamel,ops,instance,lines}.py`). `d = 3`; exponents are powers of `W` unless marked `N`; `𝔠` = bandwidth constant (flow `𝔠 = 1/6`); `N ≥ W³` so `W^x ≤ N^{x/3}`.

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `ε₁ = min(𝔡/8, 1/4)` | 1/80 (𝔡=1/10); 1/32 (𝔡=1/4) | `ε₀ < ε₁`; closure X-term needs `ε₀ < 𝔡/4` | `ε₀=0.01`: 0.0025 to `ε₁`, 0.015 to `𝔡/4` |
| 2 | `ε₀ ≤ 1/2` (target 4: `J<W^{ε₀} ≤ W^{1/2}`) | 0.01 | `ε₀ ≤ 1/2` | 0.49 |
| 3 | `J²τ_u`, `τ_u ≤ W^{-2𝔡}` (lk) | `2ε₀−2𝔡 = −0.18` | `< 0` | 0.18 |
| 4 | `τ^{1/2}J^{3/2}` (wG) | `1.5ε₀−𝔡 = −0.085` | `< 0` | 0.085 |
| 5 | `X = W^{2ε₀}(λ²W^d)^{-1/4}` (closure J-term) | `2ε₀−𝔡/2 = −0.03` | `≤ 0` (`pfStep5Alg_closure`: `ε < 𝔡/4`) | 0.03; at `ε₀=0.05, 𝔡=1/10` it is +0.05 (fails) but `0.05 ≥ ε₁` is outside the claim |
| 6 | martingale J-part `(τ^{1/2}J³)^{1/2}` | `(3ε₀−𝔡)/2 = −0.035` | `< 0` (then the J-free part dominates) | 0.035 |
| 7 | `θ' = θd(Cd+1)`, ticket `θ = ε₀/(8d(Cd+1))` | `ε₀/8 = 1.25e-3`, same for `Cd ∈ {1/2,1,4}`; `θ = 2.08e-4` at `Cd=1` | `0<θ<1`; `W^{2θ'} < W^{ε₀/4}` | `2θ' = ε₀/4` exactly: slack 0, strict `<` fails; `θ = ε₀/(16d(Cd+1))` gives `2θ' = ε₀/8`, slack 1.25e-3 |
| 8 | closure room, W-power route (a variant of `pfStep5Alg_closure` with the factor `W^{2θ'}`, +~40 lines) | `ε₀−2θ'−max(0,X) = 0.0075` | `> 0` to absorb `N^{8τ'+ε'}`·polylog | 0.0075 (ticket `θ`) |
| 9 | closure room, imported `pfStep5Alg_closure` (`τ = 𝔠ε₀/2 = 8.33e-4` in `N`; band split `Q ≤ N^{τ/2}`, `ε' = τ/2`, `τ' = τ/24`: `2θ'/3 < τ/6`) | `θ' < 𝔠ε₀/8 = 2.08e-4` | `θ'` inside | ticket `θ' = 1.25e-3`: −1.04e-3 (does not fit); `θ' = 𝔠ε₀/16`: +1.04e-4 |
| 10 | BA loss `lossE2wG` at `Λ=K₀=N^{τ'}` | `K₀²Λ⁶ = N^{8τ'}` (band `N^{6τ'}`, `PfStep5:2160 h6`) | `8τ' ≤ τ/3` at `τ'=τ/24` | `Q`-budget `N^{τ/2}`: `τ/6` left for `W^{2θ'}S_θ`, `S_θ = Σ_y e^{−(θ/2)√|y|}` is bounded uniformly in `n` by its sum over `Z^d` |
| 11 | `D* = max(D,D₀)+2d+1`, `D₀ = 2/𝔠+12d` | `D₀=48`, `D*=55` (`D=40`) | floor `(L³W¹⁸)² ≤ W^{D*−6}` needs `D*−2d ≥ D₀` | 1 (`49` vs `48`) |
| 12 | `D_u = D*+2log_W(1−u)` | at `1−u=λ²`: 50.2 for every `n` | `≥ D*−6 = 49` (target 4); `≥ D = 40` (descent, 7) | 1.2; 10.2 |
| 13 | `C_du`, exponent (target 5) | `64`, `7`: `pfStep5Grid_abs` (`PfStep5Grid:287`) is model-free, conclusion `64B⁷(R+ΔM)` | its five hypotheses at `B=(1−u_k)⁻¹`, from K1-K3 | `ops.py` max ratio 0.807 (≤1); `duhamel.py` ratio ≤ 1.9e-2 vs 64 |
| 14 | (H2): `Y = 2N(16N)⁶`, `(1−u)⁻¹ ≤ 16N` (target 3) | `n=1`: `Y = 5.1e89`; `2 ≤ 16N` | `N^ε ≥ 1/(8κ) = 1/4` | holds for all `N ≥ 1` |
| 15 | `257 ≤ N`, `W>1`, `4 ≤ log W`, `λ²W³ ≥ 1` | `n=1`: `N=5.5e11`, `log W=6.93` | all | `n=0` fails `4 ≤ log W` (3.47): instance uses `n ≥ 1`; slack 2.93 |
| 16 | eventual threshold of the closure (a conclusion, not a hypothesis) | `log10 W ≥ 3810` (`C7=18e^{8d+2}=3.5e12`, `Ctot=8.4e6`, `ε₀=0.01`, `Cu ∈ {1,100}`: the band's constants; BA's `Cq` differs) | `∀ᶠ n` | the band has the same size; instances keep it as `∀ᶠ`, never evaluate it |
| 17 | lines (viii) | `Step5IIIWalk` 1675, `Step5IIIWalk2` 1375, total 3050 (ticket 2500, ×1.22) | pre-signed split if central `> 1950`; stop line 2000 per file | **split applies**; file 1 hi 2378 (×1.42), file 2 hi 1952; file 1 central is 125 under the 1,800 reserve rule; moving the T8 (a),(b) instances (170) to file 2 gives 1505 / 1545 |

Evidence (verbatim):
```
$ python3 $S/closure.py | awk 'NR==1 || $2==1'      (Cd does not enter the exponents; Cd=1/2, 4 rows are identical)
eps0  Cd  dd  | eps1    eps0<eps1 | e_lk(J^2 tau) e_wG(tau^.5 J^1.5) e_X(closure) e_mart(J-part) | theta'(ticket) | RouteB margin | RouteA slack: ticket / theta'=c*eps0/16
0.01  1   0.1 | 0.01250 True     | -0.1800      -0.0850            -0.0300        -0.0350      | 0.00125        | +0.00750      | -0.001042 / +0.000104
0.01  1   0.25| 0.03125 True     | -0.4800      -0.2350            -0.1050        -0.1100      | 0.00125        | +0.00750      | -0.001042 / +0.000104
0.05  1   0.1 | 0.01250 False    | -0.1000      -0.0250            +0.0500        +0.0250      | 0.00625        | -0.01250      | -0.005208 / +0.000521
0.05  1   0.25| 0.03125 False    | -0.4000      -0.1750            -0.0250        -0.0500      | 0.00625        | +0.03750      | -0.005208 / +0.000521
$ python3 $S/lines.py          (components in the script: band-twin line ranges from grep of PfStep5*.lean, BA estimate per component)
Step5IIIWalk: band-twin lines 1244, BA central 1675, lo 1223, hi 2378   (stop line 2000; reserve Walk3 if > 1800)
Step5IIIWalk2: band-twin lines 824, BA central 1375, lo 1004, hi 1952   (stop line 2000; reserve Walk3 if > 1800)
total central 3050  ticket central 2500 ratio 1.22  pre-signed split threshold 1950: split applies: True
```
Rows 8-9 and 17: `pfStep5_mart_real`, `pfStep5_Zineq`, `pfStep5_final_ineq`, `pfStep5_Ctot` hard-wire `C₇ = 18e^{8d+2}` (`PfStep5:487-491, 711-855`) and are not model-free: a copy with `C₇ → Cq` (`baStep5IIITailSqQV_holds`, `Cq = 2W2²`) is +138 lines (already in 1675). `drift_sum`, `mart_sum`, `num_m`, `log_le`, `riemann_grid`, `init_le`, `fl`, `Rm` are `Sizes`/real-only and reusable by `open private`.

### (ii) One concrete nondegenerate instance

`sz0` (`L=4m, W=(2m)⁵, λ=(2m)⁻⁶, N=(WL)³`, `m=n+1`), flow `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)` (`flow_sz0`, `FlowPins:1214`), `s=1/10 < t=1/2 < 2/3 ≤ t₀` (`t0_sz0`, `FlowPins:1227`), regime `λ² ≤ 1−t`, `D=40`, `Cd=1`, `ε₀=0.01`, `θ=ε₀/(16d(Cd+1))`, `k=2` Duhamel grid. External hypotheses (Steps 1-4 pins, carried as hypotheses of the Lean instance) are not computable; their size-level premises are checked below with the limits.
```
$ python3 $S/instance.py
eps1=0.0125 eps0<eps1:True  D0=48.0 D*=55.0  theta=1.042e-04 theta'=6.250e-04 0<theta<1:True  C_du=64 exponent=7
 n   L    W        logW   N          lam        |WO lo<=lam<=1/dd | N^c<=W | lam^2<=1-t | lam^2W^3>=W^2dd | 4<=logW | N^eps>=1/(8k) | N>=257 | floor(L^3W^18)^2<=W^(D*-6) | D_u(1-u=lam^2)>=D*-6
0   4    32       3.47   2.097e+06  1.562e-02  | True  | True  | True  | True  | False | True  | True  | True  | D_u=50.200 True
1   8    1024     6.93   5.498e+11  2.441e-04  | True  | True  | True  | True  | True  | True  | True  | True  | D_u=50.200 True
2   12   7776     8.96   8.125e+14  2.143e-05  | True  | True  | True  | True  | True  | True  | True  | True  | D_u=50.200 True
3   16   32768    10.40  1.441e+17  3.815e-06  | True  | True  | True  | True  | True  | True  | True  | True  | D_u=50.200 True
10  44   5153632  15.46  1.166e+25  8.820e-09  | True  | True  | True  | True  | True  | True  | True  | True  | D_u=50.200 True
limits: W/N^(1/6) = (2m)^2/sqrt2 -> [2.828, 282.843, 28284.271, 2828427.125] ; lam*W^(1.5-dd) = (2m)^1 ->[2.0, 20.0, 200.0, 2000.0]
n=1 N= 549755813888  Y=2N(16N)^6=5.093e+89  (1-t)^-1=2 <= 16N: True
Duhamel k=2 L=8 g0=1/64 u0=0.1 uk=0.5: |A_0|_max>0 (M=6.682), Delta=0.2, err=3.069e+00, bound-with-64=1.096e+04, err<=64*bound: True
$ python3 $S/duhamel.py 1   (rows 1, 2, 5 of 8; BA-type kernel: X=MS, |X_ab|=K_ab, K doubly stochastic, K_aa=1-g0², random phases per slot, L=8, 512 sites)
g0     u0   uk    k  mode   M        R        Delta    err        (1-uk)^-7(R+DM)  ratio   ratio/64
0.0156 0.1  0.5   10  rand   7.741    1.0e-03  0.0400   7.712e-01  3.976e+01        1.94e-02 3.0e-04
0.0156 0.1  0.9   20  alt    86.662   1.0e-03  0.0400   9.560e+01  3.467e+07        2.76e-06 4.3e-08
0.5000 0.1  0.5   10  rand   5.698    1.0e-03  0.0400   2.530e-01  2.930e+01        8.64e-03 1.3e-04
$ python3 $S/ops.py | sed 's/np.float64(\([^)]*\))/\1/g'   (exact sup-norms of the 2-slot operators; ratio = norm / bound, must be <= 1)
g0       u0   uk    k   max ratios (norm/bound, must be <= 1):
0.0156   0.1  0.9   8   {'hP': 0.8068, 'hX1': 0.0997, 'hX2': 0.664, 'hTh': 0.4995, 'hThTh': 0.4982}
0.0156   0.5  0.95  6   {'hP': 0.2473, 'hX1': 0.0578, 'hX2': 0.5936, 'hTh': 0.3992, 'hThTh': 0.3962}
0.5000   0.1  0.9   8   {'hP': 0.1426, 'hX1': 0.0272, 'hX2': 0.0893, 'hTh': 0.2748, 'hThTh': 0.0744}
0.5000   0.5  0.95  6   {'hP': 0.0194, 'hX1': 0.0076, 'hX2': 0.0298, 'hTh': 0.1617, 'hThTh': 0.0252}
```
Second-order step used by `ops.py` (derived from the formulas `uKer(s,t) = 1+(t−s)θ_t`, `θ_v−θ_u = (v−u)θ_vθ_u`, `Step2Gen_thetaKer/uKer` `Chain/Step2Gen:188-193`, merged `BAuKer_eq_one_add` `BA/EKPins:62`; K1-K3 alone give only the first-order step): `‖X_j−1−Δθ_j‖ ≤ Δ²B²` per slot, `3Δ²B²` for two slots; `‖θ_t‖ ≤ (1−t)⁻¹` from K3 at `s=−1`.

Registry premises of the new public theorems (`grep` of `RBM3D/Test/Axioms.lean`; scan = `Prop` defs in a theorem's binder types that no non-private non-certificate theorem concludes, `Axioms.lean:471-492`):
```
BAStep5IIIEMatrix hits: 1 (line 240)   BAStep5IIIGood hits: 0   STDecayStronggL hits: 0   STAvgUgL 1   STGdecayWgL 1   STLmaxUgL 1   STLKUgL 1   STReg5III 1
$ grep -rn STDecayStronggL RBM3D | grep -E "(theorem|lemma) " | grep -v private   ->  BA/Step1Fam.lean:223 STDecayStronggL_congr (head ↔)   [no theorem has head STDecayStronggL; `BAFlow`, `BAReal` have heads `flow_sz0`, `BAflow_real`]
$ grep -rn "BAStep5IIIGood\b" RBM3D   ->  Step5IIIGood.lean:33 (doc), :393 (def), :419 (inside BAStep5IIIGoodThm), :635 (an `example`)   [no theorem has binder or head BAStep5IIIGood]
```

### Verdicts

- Target 1 (a),(b): PASS. (a) is `baStep5III_matrix_level` repackaged (`Step5IIIGood:349`); (b) is definitional. Registry: removing line 240 is consistent (target 1 (a) concludes `BAStep5IIIEMatrix`); **(b) as pinned has the binder `BAStep5IIIGood`, which nothing concludes: one new `owedProps` line `RBM.BA.BAStep5IIIGood` (owner U5c, `baStep5IIIGoodThm_holds`)**, or (b) is dropped/restated with the premises of `BAStep5IIIGoodThm`. The ticket's "no other change" does not hold.
- Target 2: PASS (`Step2EventsGen_Grid.meas_LM` gives `LM`, `STavgMg`, `STLKMg`; `J♯` is a `sup'` of measurable ratios; Hermitian is closed; (ii)-(iii) are `H`-free).
- Target 3: PASS (`gridRepTailBA_STeeMg_norm_le` at `η = 1/(16N)` gives exactly `2N(16N)⁶`; `η` from `gridRepTailBA_eta`, needs `N^ε ≥ 1/(8κ)`).
- Target 4: PASS (`D_u ≤ D*` from `u ≥ 0`; `D_u ≥ D*−6` from `1−u ≥ λ² ≥ W^{2𝔡−3} ≥ W^{−3}`; `baStep5III_matrix_level` and `baStep5III_scalar_flow` at `D*−6`, `1 ≤ J♯ < W^{ε₀} ≤ W^{1/2}`; rows 2, 11, 12).
- Target 5: PASS with `C_du = 64`, exponent `7` (the band's, `pfStep5Grid_abs` reused by `open private`); the kernel part is rewritten from `Step2Gen_uKer/thetaKer` plus K1-K3 (rows 13). Equivalent restatement, no paper delta beyond T2459a-f.
- Target 6: PASS. Premises of `T2493_WalkAt` are exactly the arguments of `baStep5IIIGoodThm_holds` plus `STDecayStronggL` at `s` (initial term, `Bctl_s²e^{−√r}+W^{−Dst} ≤ 4T`, `pfStep5_init_le`); inline Steps 3-4 premises equal `STLmaxUgL`/`STLKUgL` (`Chain/Step34Gen:58-68`). The closure closes (rows 3-10) with `θ` chosen after `ε₀`; **the ticket's `θ = ε₀/(8d(Cd+1))` gives `2θ'=ε₀/4`, so "`W^{2θ'} < W^{ε₀/4}`" fails strictly and the imported `pfStep5Alg_closure` does not absorb `W^{2θ'}` (row 9)**: the 1b takes `θ ≤ min(ε₀/16, 𝔠ε₀/2)/(d(Cd+1))`, or the W-power closure variant (row 8). Registry: **`RBM.BA.STDecayStronggL` is not registered and no theorem concludes it; `baStep5III_walk_at` as a public theorem with it as a binder adds it to the scan: one `owedProps` line (owner BA-V main induction, induction hypothesis at `s`)**; a public `ReadPremises` `def` as binder would add its own line, so inline the conjuncts. `STAvgUgL, STGdecayWgL, STLmaxUgL, STLKUgL, STReg5III` are registered. `BAStep5IIIWalkConcl` needs no line (`baStep5III_walk_at` concludes it); `BAStep5IIIWalk/FromWalk` have no binders in their `_holds` theorems.
- Target 7: PASS (descent `D_u ≥ D*−2d ≥ D+1`; endpoint `gridTime_last`; `Step2EventsGen_PT_of_sections`; lift by `cont_core` with the `NetLiftBA` moduli, floor `W^{−D} ≥ N^{−D/𝔠}`; `LemDecCalELip_lift` is band-only: `cont_core (P := sz.seqP)`, so the BA-direct lift (~280 lines) is needed; `0<ε`, `0<𝔡` per correction (a)).
- Target 8: PASS at `n ≥ 1` (row 15: `n=0` fails `4 ≤ log W`).
- Split: the pre-signed split applies (3050 > 1950); U5d-1 = `Step5IIIWalk` (targets 1-5, per-time layer), U5d-2 = `Step5IIIWalk2` (6-8) on `t/T2493b`; the short REQ for U5's seventh row at the 1a-audit.

Overall verdict: PASS (with the findings: θ choice, two registry lines `STDecayStronggL` and `BAStep5IIIGood`, line estimate 3050).

### (a′) Preflight corrections — Tue Oct 13 07:53:35 UTC 2026

Stage 1b (model claude-sonnet-5-5), branch `t/T2493`, base `5fbefff2`.  Four corrections to (a); none changes a verdict.
1. Registry, target 1 (b). (a) predicts a new `owedProps` line for `BAStep5IIIGood`.  It is not needed: `Step5IIIWalk_good_of_flow` (file l.102) concludes
   `BAStep5IIIGood`.  Script `scan.lean` (`RBM.Audit.scanPremises` over the final environment, with one theorem ignored at a time):
   [with everything] unregistered = []
   [without Step5IIIWalk_good_of_flow] unregistered = [RBM.BA.BAStep5IIIGood]
   [without baStep5III_EMatrix_level] unregistered = [RBM.BA.BAStep5IIIEMatrix]
   (scratch, not in the repo: `scratchpad/T2493/scan.lean` = `import RBM3D`, `open Lean Elab Command RBM.Audit`, then
    `#eval show CommandElabM Unit from do let env ← getEnv; let classified := borrowedProps ++ owedProps ++ structuralProps ++ refutedProps ++ supersededProps`
    `let run (extra : List Name) := (scanPremises env (fun n => (`RBM.Audit).isPrefixOf n || extra.contains n) (fun n => certificates.any fun (_, c) => c == n)).toList.filter (!classified.contains ·)`
    `logInfo m!"…{run []}"`, `…{run [``RBM.BA.Step5IIIWalk_good_of_flow]}`, `…{run [``RBM.BA.baStep5III_EMatrix_level]}`; the same directory has `chk.lean`, `stmtdiff.py`, `axioms.out`)
   So only the removal (i) is edited in `Test/Axioms.lean`; the ticket's "no other change" holds.
2. A binder (a) does not list.  The first full build failed: `axiom audit: 1 premise(s) that no theorem of this development proves ... [RBM.BA.STTailtoTailConclgL]`
   (hypotheses `hTT : STTailtoTailConclgL …` of public theorems; `baStep5IIIKernel_at_flow` concludes an `∃`).  Fixed: `hTT` of `Step5IIIWalk_ugenSum`/`_assemble`
   carries the unfolded text of `STTailtoTailConclgL` (`Chain/Step5Gen.lean:169`); the last `example` of the file feeds it from `baStep5IIIKernel_at_flow`.
   For U5d-2: no public hypothesis may be a `Prop` def that no theorem concludes; `STDecayStronggL` and `BAStep5IIIWalkConcl` keep the handling in (a).
3. (a) says `pfStep5_Zineq`, `pfStep5_final_ineq` hard-wire `C₇`.  Both are generic in `C7, r₁, r₂` (`PfStep5.lean:711, :820`) and are reached by `open private`; the
   copies are `Step5IIIWalk_mart_real` (`C7` a parameter) and `Step5IIIWalk_Ctot`.  File 1 is 1799 lines (row 17: central 1675, high 2378).
4. The θ budget (rows 7-9) is not a closed formula in ε₀: `Step5IIIWalk_hQ` takes `12 τ' ≤ τ/4` and `2 θ (Cd+1) ≤ τ/4`, `τ` the closure exponent
   (after `Cc`, `Cq`, `ε₀`); θ is chosen after τ, still inside the walk, before the good event of U5c (which quantifies `τ' D₁ θ`).

## (b) Script output — Tue Oct 13 07:53:35 UTC 2026

Split: U5d-1 only (`BA/Step5IIIWalk.lean`: targets 1-5 and the per-time layer); `BA/Step5IIIWalk2.lean` (targets 6-8) waits for the REQ and runs on `t/T2493b`.
```
$ git -C ../RBM3D-wt/T2493 log --oneline | head -4        (t/T2493, base 5fbefff2)
b430f3c2 T2493: U5d-1 Step5IIIWalk, instance docstring
46e6e852 T2493: U5d-1 Step5IIIWalk, section 3: instances of targets 1-5, loss budget, registry (import line, BAStep5IIIEMatrix owed line removed)
a9cb4fac T2493: U5d-1 Step5IIIWalk, section 2: per-time layer (...)
aa89b7f7 T2493: U5d-1 Step5IIIWalk, section 1: targets 1-5 (...)
$ lake build RBM3D.BA.Step5IIIWalk                  ->  Build completed successfully (4105 jobs).
$ lake build     (full library; RBM3D.lean import line + Test/Axioms.lean edit; final run 07:45 UTC)
   Build completed successfully (4356 jobs).      EXIT 0
   axiom audit: 14712 theorems, 4566 definitions, 0 axioms in `RBM`   [premises found by scanning: 127 (borrowed 1, owed 60, structural 46, refuted 6, superseded 14)]
$ lake env lean docs/tickets/checks/T2493-check.lean  ->  exit 0, 0 errors
$ wc -l RBM3D/BA/Step5IIIWalk.lean                   ->  1799   (stop line 2000 per file; the 1a's reserve rule 1800 not reached)
  sections (grep '^/-! ## '):  1 targets 1-2: l.72-217 | 2 target 3: 218-244 | 3 target 4: 245-301 | 4 target 5: 302-694 | 5 a priori: 695-789 | 6 ugenSum: 790-897
                               7 mart_real: 898-981 | 8 assembly: 982-1176 | 9 per-time: 1177-1451 | 10 loss budget: 1452-1520 | 11 instances: 1521-1799
$ git diff --stat main...t/T2493       RBM3D.lean | 1 +,  RBM3D/BA/Step5IIIWalk.lean | 1799 +,  RBM3D/Test/Axioms.lean | 1 -   (3 files; the only importer of the new file is RBM3D.lean)
```
**Axioms** (`#print axioms`, all 32 public declarations of the file, theorems and the def `Step5IIIWalk_Ctot`; 0 lines outside `[propext, Classical.choice, Quot.sound]`):
```
baStep5III_EMatrix_level        [propext, Classical.choice, Quot.sound]
baStep5IIIGood_bundle           [propext, Classical.choice, Quot.sound]
baStep5IIIJsharp_measurable     [propext, Classical.choice, Quot.sound]
baStep5III_goodMeas             [propext, Classical.choice, Quot.sound]
baStep5III_crudeQV              [propext, Classical.choice, Quot.sound]
baStep5III_walkLevel            [propext, Classical.choice, Quot.sound]
baStep5III_duhamel              [propext, Classical.choice, Quot.sound]
```
**Target statements** (extracted by script from the file, whitespace normalized; l. = line of the `theorem`):
```
-- 79: theorem baStep5III_EMatrix_level (d : ℕ) :
   ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D D' Λ K₀ J θ Cd : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), D' ≤ D → BAStep5IIIEMatrix sz
   lam0 E n u D Λ K₀ J θ Cd H → BAStep5IIIEMatrix sz lam0 E n u D' Λ K₀ (BAStep5IIIJsharp sz lam0 E n D' u H) θ Cd H
-- 87: theorem baStep5IIIGood_bundle :
   ∀ (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (D Cd : ℝ), BAStep5IIIGood sz z s t D Cd → ∀ τ' D₁ θ : ℝ, 0 < τ' → 0 < D₁ → 0 < θ → θ < 1 → ∀ᶠ n in atTop, ∀ u : TimeIcc s t
   n, ∃ G : Set sz.SeqΩ, Sizes.seqP (sz.withLam 0) Gᶜ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) ∧ ∀ ω ∈ G, BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n
   (u : ℝ) D (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ') (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n D (u : ℝ) (sz.seqHflowBA (BAflowLam0 sz z)
   n (u : ℝ) ω)) θ Cd (sz.seqHflowBA (BAflowLam0 sz z) n (u : ℝ) ω)
-- 135: theorem baStep5IIIJsharp_measurable (d : ℕ) :
   ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D u : ℝ), Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => BAStep5IIIJsharp sz lam0 E n D
   u H
-- 156: theorem baStep5III_goodMeas (d : ℕ) :
   ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ θ Cd : ℝ), MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ | BAStep5IIIEMatrix sz
   lam0 E n u D Λ K₀ (BAStep5IIIJsharp sz lam0 E n D u H) θ Cd H}
-- 225: theorem baStep5III_crudeQV (d : ℕ) :
   ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n → ∀ H :
   Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian → ∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)), ‖STeeMg (baStep2Mat sz (BAflowLam0
   sz z) (BAflowEs sz z)) n u H σ b b'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6
-- 253: theorem baStep5III_walkLevel :
   ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → STReg5III sz s t → ∀ Dst τ' θ Cd ε₀ : ℝ, 0 ≤ τ' →
   ε₀ ≤ 1 / 2 → (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (Dst - 2 * 3)) → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n)
   (H : Matrix (Idx 3 (sz.L n) (sz.W n)) (Idx 3 (sz.L n) (sz.W n)) ℂ), BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) Dst (((sz.size n : ℕ) : ℝ) ^ τ')
   (((sz.size n : ℕ) : ℝ) ^ τ') (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (u : ℝ) H) θ Cd H → BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n
   (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H < ((sz.W n : ℕ) : ℝ) ^ ε₀ → BAStep5IIIEScalar sz n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u :
   ℝ)) (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ') (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u :
   ℝ)) (u : ℝ) H) ∧ BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (((sz.size n : ℕ) : ℝ) ^ τ')
   (((sz.size n : ℕ) : ℝ) ^ τ') (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H) θ Cd H
-- 677: theorem baStep5III_duhamel (d : ℕ) :
   ∃ Cdu : ℝ, 0 < Cdu ∧ ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ), 0 < κ → BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → ∀ (Δ M R : ℝ) (σ : Fin 2 →
   Bool) (k : ℕ) (u : ℕ → ℝ) (A F Rem Mart : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ), 0 ≤ Δ → 0 ≤ u 0 → (∀ j, u (j + 1) = u j + Δ) → u k < 1 → (∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) →
   (∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R) → (∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j, (Step2Gen_ThetaN (baFM sz lam0 E) n σ (u i) (A i) b + F i b) +
   Rem j b + Mart j b) → ∀ a, ‖A k a - Step2Gen_UN (baFM sz lam0 E) n σ (u 0) (u k) (A 0) a - ∑ j ∈ Finset.range k, (Δ : ℂ) * Step2Gen_UN (baFM sz lam0 E) n σ (u j) (u k)
   (F j) a - ∑ j ∈ Finset.range k, Step2Gen_UN (baFM sz lam0 E) n σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤ Cdu * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M)
```
**Statement diff against the pins** (`stmtdiff.py`: the `T2493_*` body of `docs/tickets/checks/T2493-check.lean` vs the theorem statement, whitespace normalized) and the auditor's examples:
```
T2493_EMatrixLevel   vs baStep5III_EMatrix_level      : IDENTICAL (normalized whitespace) [278 / 278 chars]
T2493_GoodBundle     vs baStep5IIIGood_bundle         : IDENTICAL (normalized whitespace) [568 / 568 chars]
T2493_JsharpMeas     vs baStep5IIIJsharp_measurable   : IDENTICAL (normalized whitespace) [170 / 170 chars]
T2493_GoodMeas       vs baStep5III_goodMeas           : IDENTICAL (normalized whitespace) [228 / 228 chars]
T2493_CrudeQV        vs baStep5III_crudeQV            : IDENTICAL (normalized whitespace) [431 / 431 chars]
T2493_WalkLevel      vs baStep5III_walkLevel          : IDENTICAL (normalized whitespace) [1314 / 1314 chars]
T2493_Duhamel        vs baStep5III_duhamel            : IDENTICAL (normalized whitespace) [820 / 820 chars]
ALL IDENTICAL
$ lake env lean chk.lean   (the seven `T2493_*` defs copied from the check + `example : T2493_X := name` for the seven names)  ->  0 errors
```
**Compiled nonempty instances** (12 `example`s, section 11, l.1546-1799; `sz0`, `zSeq`, `flow_sz0`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `s ≡ 1/10 < t ≡ 1/2 < t₀`, `Cd = 1`):
```
1546 targets 1 (a),(b): ∃ n, u, ω∈G (G the good event at D=40): EMatrix at (40, J♯) and, by (a), at (30, J♯_30); the four carrier predicates stay hypotheses
1572/1577/1583 target 2 at n=1 (L=8, W=1024), u=1/2, D=40: J♯ measurable; {J♯ < W^{1/100}} measurable; the EMatrix set measurable
1590 target 3 at t ≡ 1/2   |  1608 target 4 at D*=46, τ'=1/100, θ=1/10, ε₀=1/100 (flow, regime, floor discharged; floor from Step5IIIGood2_sz0_floor)
1642 target 5 at n=1, σ=(+,-), k=2, u_j = 1/10 + j/10, A_j ≡ j+1 (≠ 0), M=3, R=0, F defined from the increments, BAReal from BAflow_real
1694 pertime∘target 1(b)∘target 4 on G | 1734 a priori | 1743 xx | 1758 loss budget (τ=1, τ'=1/48, θ=1/20) | 1768 ugenSum with hTT := baStep5IIIKernel_at_flow
```
**Registry** (script `scan.lean`, final environment; the audit at RBM3D.lean:588 passes): `BAStep5IIIEMatrix in owedProps = false`, `BAStep5IIIGood in any list = false`; the three `unregistered` lines are in (a′)1.
**Name clash** (`git grep -w` of the 32 new public names): main@3238c365 `RBM3D`, `RBM3D.lean`: 0 files; 509 branches `t/*`: 0 hits outside `BA/Step5IIIWalk*`.
**Greps** on the new file: C1 pattern 0; `STGridRepNgL|…|≤ A \*` 0 (the two docstring hits of `|E|` were reworded); `withLam` outside `seqP (sz.withLam 0)`/`pathP (sz.withLam 0)` 0;
`(def|abbrev|structure) (BAStep5IIIEScalar|…|STGridRepNAtgL)` 0; `sorry|admit|native_decide|^axiom` 0.
**Ports** (all sources are RBM3D band files, not edited; commits `git log -1 --format=%h -- file`: PfStep5 e2ec919c, PfStep5Grid 0f44a56c, PfStep5Alg 14513ee3, NQGood1 691566a6,
EigenMeasurable a52eb855; nothing from `../RBM1D`/`../RBM2D`, so no diff-stat): `open private` (2 commands, 26 names): `pfStep5Grid_{abs,slot,slot_apply,slot_add,slot_sub,slot_smul,slot_one,norm_slot,sum2,update2,update2',alg,inv_le}`,
`pfStep5_{drift_sum,mart_sum,Zineq,final_ineq,init_le,tailTD_mono,tailTD_floor,tailTD_nonneg,lvl,W2_le,rpow_le,y_three_half,sizes}`.  Copies adapted to BA: `mart_real` (`PfStep5:737`), `Ctot` (`:490`),
`assemble` (`:857`), `ugen_term`/`ugenSum'` (`PfStep5Alg:181, :236`), `pertime` (`PfStep5:1054`, here through `baStep5IIIEdet_holds`), `xx` (`:1326`), `apriori` (`:1269`), `norm_loopFine_le`
(`NQGood1:916`), `meas_herm` (`EigenMeasurable:295`), the Duhamel operators and norms (`PfStep5Grid:584-883`, `:892`).

**Narrative** (ticket report order):
(1) File 1 = 1799 lines < 2000.  Split decision of (a) confirmed and followed; file 2 reads only public `Step5IIIWalk_*`/`baStep5III*` names (no `open private` across the row).
(2) Numerics are those of (a); the inequalities that depend on them are compiled: `baStep5III_walkLevel` (`D_u ≥ D*−6` from `lam² ≤ 1−u`, `1 ≤ lam² W³`), `Step5IIIWalk_hQ`, `Step5IIIWalk_apriori` (`N ≥ 300`).
(3) Route.  T1: `baStep5III_matrix_level` re-read at `BAStep5IIIEMatrix`; (b) is `filter_upwards` on the hypothesis `BAStep5IIIGood`.  T2: `Finset.measurable_sup'`, F9 (`Step2EventsGenTw_baGrid`), `MeasurableSet.const` for (ii)-(iii),
(vi) rhs; `Step5IIIWalk_good_transfer` moves `G ⊆ seqHflowBA⁻¹ S` to `Hpath` by `Step2EventsGenTw_baLaw`.  T3: `gridRepTailBA_STeeMg_norm_le` at `η = 1/(16N)`, `gridRepTailBA_eta`.
T4: `baStep5III_scalar_flow` twice (at `D*−6` with `J = 1`, then at `D_u`), `pfStep5Grid_level`, `baStep5III_matrix_level` at `D_u ≤ D*`.  T5: K1 gives `u_{s,t} = 1 + (t−s)θ_t`; K3 at `s = −1` gives
`‖θ_t‖ ≤ (1−t)⁻¹`; K1 with `u = −1` gives `θ_w − θ_v = (w−v)θ_wθ_v`; K2 gives `‖u_{v,w}‖ ≤ (1−v)/(1−w)`; the band's `pfStep5Grid_abs` closes, `Cdu = 64`, exponent 7 (no `|E| ≤ 2`, no `‖m‖ = 1`).
Per-time layer: pertime = T4 + `baStep5IIIEdet_holds` + the bridges `STELKLKMg_eq_STelklkMg`, `STEGtMg_eq_STegtMg` (`baStep2Mat_listLink`); the QV factor `W^{2θ'} S_θ` of (vi) sits in `Q ≥ lossE2wG·W^{2θ'}S_θ`.
(4) Statement diff: identical to the pins, up to whitespace (above); `Cdu = 64` and the exponent 7 are the 1a's (row 13), reported.
(5) Premises read in file 1: `STAvgUgL`, `STLmaxUgL`, `STLKUgL`, `STGdecayWgL` (hypotheses of `Step5IIIWalk_good_of_flow`, as of `baStep5IIIGoodThm_holds`); none other of `STIngR5gL` (the walk is file 2).  Carried unread: all others.
(6) UBA-C1 table as used.  Rows 1, 2: none.  Row 3: `baStep2Mat` at `BAflowLam0`, `η_u ≥ 1/(16N)` from `Im z`, `κ ≤ Im m`; no crossing.  Row 4: regime, `WO`.  Row 5: `u_k < 1`, `BAReal`.  Row 7 (U5d-2): —.
Crossing: for `BAStep5IIITailSqQV` it is in `Step5IIIWalk_xx` (file 1): `lam0 ≤ sz.lam` through `baStep5III_lam0_le_lam` at `0 < g₀` (`BAflow_lam0_window`), per index under `∀ᶠ n`; for `BAStep5IIIKernel` it is inside the merged `baStep5IIIKernel_at_flow`; no other.
C1: `Cq = Cq(d, κ, 𝔡)` (from `baStep5IIITailSqQV_holds`) comes before `(ε, 𝔠, sz, z)`; `Cdu = 64`; no entry-level bound, no `|E|`, no `M = mI`; TN-C4: 0 hits; T2492 F1: every per-index fact is under `∀ᶠ n` or at one `n`.
(7) Paper-delta candidates: none new beyond T2459a-f (see (d)).

## (c) Verified Mathlib names (all used in the compiled file; each checked by `lake build`)

Matrix.linfty_opNorm_def, Finset.measurable_sup', Finset.single_le_sum, Finset.sum_range_sub, Finset.sum_div, Finset.sum_apply, Finset.sup_le, Real.rpow_two, Real.rpow_natCast, Real.rpow_neg,
Real.rpow_lt_one_of_one_lt_of_neg, Real.rpow_le_rpow_of_exponent_le, Real.one_le_rpow, Real.log_nonneg, Real.log_nonpos, Real.coe_toNNReal, Real.tendsto_log_atTop, Complex.norm_real,
Complex.norm_natCast, ENNReal.one_le_ofReal, MeasurableSet.const, MeasurableSet.iInter, measurableSet_le, measurableSet_lt, Set.ofPred_and, Set.eq_univ_of_forall, smul_right_injective,
mul_apply_eq_comp, one_apply_eq_self, pi_norm_le_iff_of_nonneg, norm_le_pi_norm, ContinuousLinearMap.ext, Nat.one_le_iff_ne_zero, isClosed_eq, continuous_star; tactic `linear_combination (norm := module)`.
Verified deprecated: `Set.setOf_and` (warning "use `Set.ofPred_and`"); used `Set.ofPred_and`.

## (d) Open issues and paper-delta candidates

1. Interface for U5d-2 (public, stem `Step5IIIWalk_`/`baStep5III*`, all with the standard three axioms).  Path induction: `_pertime` (flow, `∀ᶠ n`, `u : TimeIcc`), `_good_transfer`, `baStep5IIIGood_bundle`/`_good_of_flow`,
   `_apriori`, `_xx` (`∃ Cq` before `Dst`; `∃ D₂` after it), `_assemble` (+ `_Ctot`, `_Ctot_ge`), `_mart_real`, `_init`, `_drift_eq`, `_ugenSum`, `_duhamel`, `_hQ`.  Numerics left to file 2: closure `τ` by `pfStep5Alg_closure`
   at `C = Step5IIIWalk_Ctot d Cc Cq` (`Cc` from `baStep5IIIKernel_at_flow`), then `τ'` with `12 τ' ≤ τ/4`, `θ` with `2θ(Cd+1) ≤ τ/4`, `Dst`, `Dg`, the grid `K`, `pfStep5_fl/_Rm/_hKD/_hlabel` by `open private`.
2. The registry for file 2: `STDecayStronggL` (binder of `T2493_ReadPremises` if public) and `BAStep5IIIWalkConcl` as in (a) and in the ticket's registry paragraph (ii); the new rule of (a′)2.
3. The REQ for U5's seventh row is the dispatcher's at the 1a-audit (CONTROL); nothing in this branch depends on it.  `Step5IIIWalk2` is not created.
4. Paper-delta candidates: none new.  Equivalent restatements already covered: Duhamel form at the BA kernel from K1-K3 (ticket answer (4)), near cut `2ℓ*` (T2459b), J-free factor (T2459f), `D_u ≥ D*−2d` read at `d = 3` as `D*−6`.
