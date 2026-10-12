Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 13:14:18 UTC 2026

Notation: `N=(WL)^d`, `W=sz.W n`, `Γ:=1/κ_m` where `κ_m>0` is the lower bound of `Im(C.m n)`; `A:=1/𝔠`; `r(k):=2(k-1)+1+C₀`;
`Q(k):=2D'+A·r(k)+1`. Band sources are `DecayLoopB.lean` (`B`), `DecayLoopA.lean` (`A`), `Step2Events.lean` (`E`).

### (i) Exponent table (value at the instance of (ii): `d=3, κ=ε=𝔡=1/10, 𝔠=1/6, Cd=1, τ'=1/10, D'=1`)

| # | quantity | constraint (source) | value / slack |
|---|---|---|---|
| 1 | `d` | `2≤d` is all the generic proof uses (`L²≤L^d`, `B:1122`); statements keep `3≤d` (band K-decay needs it) | `3`; slack 1 |
| 2 | `κ_m`, `Γ` | `η⁻¹≤ΓN` from `1-u≥N⁻¹`, `η=(1-u)Im m≥(1-u)κ_m` (`B:1515`). Band `κ_m=√κ/2` (`B:1108`), `Γ=2/√κ`; BA `κ_m=κ`, `Γ=1/κ` (`EMn2BA.lean:125`) | band `Γ=6.3246`; BA `Γ=10` |
| 3 | `𝔠`, `A` | `N≤W^A` (`Bandwidth`) | `A=6`; at `n=0`: `ln N^{1/6}=2.426 ≤ ln W=3.466` |
| 4 | `𝔡` | `lam²W^d≥W^{2𝔡}≥1` gives `STWB≤2` (`B:1161`) and `W^{-d}≤lam²` (`B:1485`) | `2.079 ≥ 0.693` at `n=0`; `lam≤𝔡⁻¹`: `-4.159≤2.303` |
| 5 | `Cd`, `C₀`, `P_n` | `C₀=max(Cd,0)+1`; `P_n=((1-s)/(1-u))^{Cd}Bctl^{1/5}≤N^{C₀}` from `(1-s)/(1-u)≤N`, `Bctl≤2≤N` (`B:1531`) | `C₀=2`; slack factor `N/2` |
| 6 | `Q(k)` | K-decay used at `(τ'/2,Q(2))` for the far pair and `(τ',D'+1)` for `K^{(k)}` (`B:1444-1446`) | `Q(2,3,4)=33,45,57` |
| 7 | `Θ=2`, `W` floor | `W≥16Γ^{2(k-1)}(2+Θ)=64Γ^{2(k-1)}`, `W≥2` (`DecayLoopB_alg`, `B:1212`) | `y≥4.8, 10, 21` for `k=2,3,4` (script) |
| 8 | `τ'` links | `k-1≤W^{τ'/2}`; `W^{τ'/4}≥4Qk/τ'` (`B:1310`); far `dist≥ℓW^{τ'}/(k-1)` gives `dist≥ℓW^{τ'/2}` and `(dist/ℓ)≥(W^{τ'/2}/k)²` (`B:1345`) | binding: `y≥2.36e27, 7.2e29, 4.8e31` (eventual in `n`, as the band) |
| 9 | closure | `Λ²≤Γ^{2(k-1)}(2+Θ)N^{r}W^{-Q}`, `N≤W^A` give `Λ≤2Γ^{k-1}W^{-D'-1/2}`; `2Λ+Kc≤W^{-D'}` | `(2Λ+Kc)/W^{-D'}≈10^{-73}` at `y=10^30`; margin `W^{-1/2}` |
| 10 | window | `t<1` (`flowOK_T`); `1-u≥N⁻¹`: derived from the far premise in the U form (`ℓ_u<L ⇒ g²<L²(1-u)`, `W^{-d}≤g²`, `B:1122`); in the PT form (target 5) a hypothesis `∀ᶠ n, N⁻¹≤1-t_n` | `1-t=15/16≥N^{-1+ε/2}`; BA: `Im z/2≤1-T0` (`EMn2BA.lean:111`) and `Im z≥N^{-1+ε}` give it once `N^ε≥2` |
| 11 | `STBdata` | `cB=(𝔡⁻²+1)⁻¹`, `c=min(2𝔡𝔠,ε)/2` (`Step2Iterate:1049ff`), `N^c≥5` | `cB=0.0099`, `c=1/60`; `N≥8.67e41` |
| 12 | `ε₀`, `Ψ` | `ε₀=dc/4≤d/2`; `Ψ²=(1+cB⁻¹)Bctl`, `W^{-d/2}≤Ψ≤W^{-ε₀}` needs `W^{dc/2}≥1+cB⁻¹` (`E:385-399`) | `ε₀=0.0125<1.5`; `W≥2.21e80`; `(1+1/cB)cB=1+cB≥1` |
| 13 | `ε₁`, `δ₀`, `Λ` | (E1) `N^{ε₁}Bctl^{1/4}≤δ₀`; `Bctl≤N^{-c}` so `ε₁≤c/4`, `δ₀=1`; (E3) `Λ≥N^{ε₁}`, (E4) `Λ≥2N^{ε₁}` | `ε₁=c/8`: `N^{-0.00208}≤1` |
| 14 | grid | `K=⌈N^{CK}⌉`, `(K+1)·#V≤N^{CK+5}` for `#V≤N⁴` (`ST_hcard:522`, `N≥3`) | `1e9≤1e18` at `N=1000, CK=1` |
| 15 | (E5), `Dm` | `a+C≤Dm` with `a=D'+1`, `C=3` (`ST_card_lab_le:172`, `N≥4`); `2N^{-(D'+1)}≤N^{-D'}` iff `N≥2` | `Dm=D'+4=5`, **slack 0** (sharp) |

Carrier facts that replace band objects (hypothesis rules: none uses `‖m‖=1`, scalar `m`, `mE`, `zt`, `etaT`, `STFlow`, `lemT`, `pathP/H`):

| fact | statement over `C` / `Cm` | band source | BA source / owner | targets |
|---|---|---|---|---|
| F1 adm | `flowOK κ ε 𝔠 𝔡 → sz.Admissible 𝔠 𝔡` | `Step2Data.flowOK_adm` (`Step2Gen:111`) | `baStep2Data` (`Step2BA.lean`, merged) | 4-6, 8-11 |
| F2 `T0<1` | `0<κ → flowOK … → T0 n<1` | `flowOK_T` | `baStep2Data` (merged) | 4-6, 8-11 |
| F3 spectral | `C.eta n u=(1-u)·(C.m n).im`, `κ_m≤(C.m n).im` (so `eta>0` for `u<1`) | `etaT=(1-t)(mE E).im` (`GLoop:75`), `Im mE≥√κ/2` | `etaOf m t=(1-t)m.im` (`GLoopFlow:58`), `EMn2BA.lean:125` (merged) | 4-6, 9, 10 |
| F4 Ward pair | `∀ n k≥2 σ a, ∃ c₁ c₂, diam_∞ a≤(k-1)|c₁-c₂|_∞ ∧ ∀ u∈[s_n,t_n] ω, 0<η → ‖C.L n u σ a ω‖²≤η⁻¹^{2(k-1)}‖C.L n u (+,-) (c₁,c₂) ω‖`, `η=C.eta n u` | `DecayLoopB_pair` (`B:1065`; `H` Hermitian, `η≤|Im z|`) | `DecayLoopB_pair` on `loopFine` of `seqHflowBA`; Hermitian: `ConArg_seqHflowBA_isHermitian` (`ConArg:310`, private); `ztOf_im` (`GLoopFlow:64`). Owner T7-BA, no new mathematics | 4-6 |
| F5 K far decay | `STKcalDecaygL C` (check-file shape kept: `ℓ¹` `KLmaxDist`, `u∈[0,1)`, `∀ᶠ n` after `τ,D`) | `inst_stKcalDecay_admissible` (`KDecay:976`) at `E n` | U2-BA `BAKcalDecay` (owed, DECISIONS §264) | 4-6, 7 |
| F6 range | `∀ᶠ n, N⁻¹≤1-t_n` | `v3_premises_of_stFlow` (`A:994`) | `EMn2BA.lean:111` + `TwistLoop.lean:88` (private, merged) | 5 only |
| F7 rot3 | `C.L n t ![a,b,b] ![x,y,z] ω=C.L n t ![b,b,a] ![y,z,x] ω` | `STB_loop_rot` (`E:1283`, private) | trace cyclicity of `loopFine` (as `Step2Gen_loopFine_swap`); owner T1-BA | 11 (bridges) |
| F8 family | targets 8-10 take the pins in family shape `(law,Flow,mk,T0)` with `mk` valued in `Step2Mat`, since `STLWTgL`, `STEMn2ExpgL` quantify over all `sz, z`; F1-F2 are then `∀ sz κ ε 𝔠 𝔡 z` statements | `bandStep2Data` | `baStep2Data` | 8-10 |

### (ii) One concrete nondegenerate instance (`d=3`)

Data: the merged flow instance of `DecayLoopB.lean:2236-2250, 2396` (`sz0`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `κ=ε=𝔡=1/10`,
`𝔠=1/6`, `Admissible (1/6)(1/10)`, `flow_z0`), window `[s,t]=[0,1/16]` (`≤ lemT z0`), `Cd=1`, `τ'=1/10`, `D'=1`, `k∈{2,3,4}`. With `y:=2(n+1)`:
`L=2y`, `W=y^5`, `N=8y^{18}`. Every hypothesis of the deterministic parts of targets 4-6, 8-11 is read off in the table and checked below
(`Admissible`, `WO`, window, closure, `STBdata` constants, event exponents, union bound, grid count). The probabilistic conclusions and the
inputs F4-F5, `STGdecayWgL`, `STScaleInvgL`, `STLWTgL`, `STEMn2ExpgL`, `STStep1WeakgL`, `STDecaygL` are other gates' outputs (hypotheses).
The thresholds are eventual in `n`, exactly as in the band (`B:1444-1446` uses `∀ᶠ`); the binding one is row 8 (`y≥2.4e27` for `k=2`).

```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2454/inst.py
Admissible(1/6,1/10) at sz0: N^c<=W : ln(N^(1/6))-lnW = 2.426 - 3.466 (y=2: worst case y=2)
WO lower: -(d/2-dd)lnW = -4.852 <= ln lam = -4.159 ; ln lam <= ln(1/dd)=2.303
lam^2 W^d >= W^{2dd}: 2.079 >= 0.693
Gamma=2/sqrt(kappa)=6.3246, A=6.0, C0=2.0
k=2 r=5.0 Q=33.0 W>=64 Gam^(2(k-1)): y>=4.8 ; k-1<=W^(tau/2): y>=2 ; W^(tau/4)>=4QK/tau: y>=2.36e+27 ; N<=W^A (sz0): y>=2
   closure at y=1e30: (2Lam+Kc)/W^-D' = 2.530e-74 (<=1 needed)
k=3 r=7.0 Q=45.0 W>=64 Gam^(2(k-1)): y>=10 ; k-1<=W^(tau/2): y>=16 ; W^(tau/4)>=4QK/tau: y>=7.23e+29 ; N<=W^A (sz0): y>=2
   closure at y=1e30: (2Lam+Kc)/W^-D' = 1.600e-73 (<=1 needed)
k=4 r=9.0 Q=57.0 W>=64 Gam^(2(k-1)): y>=21 ; k-1<=W^(tau/2): y>=81 ; W^(tau/4)>=4QK/tau: y>=4.79e+31 ; N<=W^A (sz0): y>=2
   closure at y=1e30: (2Lam+Kc)/W^-D' = 1.012e-72 (<=1 needed)
window [0,1/16], y=2: N^(-1+eps/2)=9.87e-07 <= 1-t=0.9375 ; 1/(1-t)=1.067 <= N=2.1e+06 (hnu: 1/N<=1-u)
window [0,1/16], y=4: N^(-1+eps/2)=7.03e-12 <= 1-t=0.9375 ; 1/(1-t)=1.067 <= N=5.5e+11 (hnu: 1/N<=1-u)
window [0,1/16], y=100: N^(-1+eps/2)=8.75e-36 <= 1-t=0.9375 ; 1/(1-t)=1.067 <= N=8e+36 (hnu: 1/N<=1-u)
STBdata: cB=0.00990 c=min(2dd c,eps)/2=0.01667 ; N^c>=5 iff ln N>=96.6 (N>=8.67e+41)
eps0=d c/4=0.01250 in (0,d/2=1.5); 1+1/cB=102.0 <= W^{dc/2}=W^0.02500 iff W>=2.21e+80
(E1) eps1=c/8=0.00208, N^{eps1}Bctl^{1/4}<=N^{eps1-c/4}=N^-0.00208<=1=delta0 for all N>=1
(E5) Dm=5: union bound a+C=(D'+1)+3=5<=Dm slack 0; 2N^-(D'+1)<=N^-D' iff N>=2
grid: (K+1)*N^2 = 1e+09 <= N^(CK+5)=1e+18 at N=1000, CK=1
$ python3 -I .../scratchpad/T2454/ext.py        # external hypotheses: limit computations
far premise ell*W^tau<=diam, tau=1/10, y=2,4,100,1e6: [True, True, True, True]  tau=1/5: [True, True, True, True]
STGdecayWgL rhs at far pair (dist=y, ell<=1): exp(-sqrt y)<=W^-33=y^-165 iff y>=6.73e+06; below that the exp term dominates the floor
STKcalDecaygL at tau=1/10: premise needs dist>=W^(1/10)=y^(1/2); max dist L/2=y: slack factor y^(1/2) (y=1e6: 1000)
```

External hypotheses (limit computations above): the far premise `ℓ_0 W^{τ'} ≤ diam_∞ a` is nonempty at every `y` iff `τ'≤1/5`
(`W^{τ'}=y^{5τ'}≤y`, `ℓ_0=1`; used `τ'=1/10`, `τ'/2`, slack `y^{1/2}`), so F5 and `STGdecayWgL` are not vacuous at `sz0`
(`DecayLoopB_sz0_far_nonempty_U`, `B:2360`, is the Lean witness of the same set). At the far pair the exponential term of `STGdecayWgL`
dominates the floor `W^{-33}` only for `y<6.7e6`, so the hypothesis is a genuine decay input for large `y`, not a consequence of the floor.

## Verdicts and design answers (mathematics only; the compile probe is the next step)

- **1 PASS.** Body = `twSteps` conjunct 4 (`TwistPins.lean:139-142`) and `T2454_DecayLoopUgL` coincide as text. The band bridge is a binder-order swap
  (`∀ τ', 0<τ' → ∀ D', 0<D'` to `∀ τ' D', 0<τ' → 0<D'`), not `Iff.rfl`; the proof is `fun h k hk τ' D' hτ' hD' => h k hk τ' hτ' D' hD'` (math: none).
- **2 PASS.** Same binder order in the band and the check shape, so `Iff.rfl` is expected.
- **3 PASS, shape kept** (`ℓ¹` `KLmaxDist`, `u∈[0,1)`, `∀ᶠ n` after `τ,D`). Reason: the proof consumes it only at `(τ'/2,Q(2))` on `|c₁-c₂|_{ℓ¹}≥ℓW^{τ'/2}`
  (`B:1371`) and at `(τ',D'+1)` on `diam_∞≤KLmaxDist` (`B:854`); the energy quantifier is removed by
  `E:=E n` with `|E n|≤2-κ`, and the band `Q`-clause (`W^{-Q}≤g`) is discharged by `WO` (`Q=d/2`, `KDecay:985, 990`), so no window change is needed.
- **4, 5, 6 PASS** with F1-F5 (F6 for 5). Target 6 does not need `Step2Data`'s `L_swap`; `Cm : Step2Data sz` is used only for F1-F2; `FlowFM`
  plus F1-F5 suffices if F1-F2 are passed as the two scalar facts `Admissible` and `∀ n, t n<1` (lower dependency; recommended). Constants of the
  proof: `Γ=1/κ_m`, `A=1/𝔠`, `C₀=max(Cd,0)+1`, `Q(k)` of row 6; no new loss. No new field of `FlowFM` or `Step2Mat` is needed (F3-F7 are hypotheses).
- **7 deferred to U2** (stop rule): `Chain/` contains no `Step34Gen` on `main` (`ls RBM3D/Chain`: Carrier, GridDuhamelGen, LWGen, NewKLKGen, Step2Gen, Step2Kern).
  Inputs when it is proved: `STDecayLoopUgL`, F5, `STKboundgL` (generic form is per time sequence; the band uses the `TimeIcc`-uniform `stKbound_timeIcc`, so U2 supplies the uniform form).
- **8 PASS** (`STScaleInvgL`: expected `Iff.rfl`; `ST_LW_sectionsg`: `Ψ²=(1+cB⁻¹)Bctl`, `ε₀=dc/4`, rows 11-12; F8 family shape).
- **9 PASS** with one `Iff.rfl` failure to name: the band event uses `Λ/((mE E).im*(1-u))`, the carrier `Λ/C.eta`; with F3 `C.eta=(1-u)·Im m` they agree up to
  `mul_comm`, and the generic proof needs only `0<C.eta` (F3) and `Λ·η⁻¹x=Λ/η·x`; no bridge identity is required for the theorems, only for `bandFM` readings of the events.
  (E1) needs no spectral fact; (E2) takes `STDecaygL C μ s` and the comparison `hcmp` as hypotheses; (E3)/(E4) take `STLWTgL`/`STEMn2ExpgL`/`STScaleInvgL` in family shape (F8).
- **10 PASS** (`ST_good_probg`, `STGoodAtg`): pure probability and arithmetic (rows 13-15); `hident` uses `STgDriftg`; no spectral fact. `Dm=D'+4` is sharp (row 15).
- **11 PASS, keep both bridges**: `STBdatagL` is a pin with `ST_Bdata_holds` as the band proof (rows 11, F1-F2; BA numbers: `1-T0≥Im z/2`, constants `cB,c` unchanged since `Bparam`
  depends on `sz.lam` only). The bridges need exactly F7 (`STB_EGt_eq_LWE` is the rotation of the 3-loop; rotate `(a₀,y,a₁)` to `(y,a₁,a₀)`) and `ε₀≤d/2` (`STB_eps_le`, `E:1320`, from `W→∞`).
  Band proofs: `STLWB_of_LWterm` `E:1355-1426` (72 lines), `STLWT_of_LWtermExp` `E:1427-1455` (29 lines), each below the 150-line rule.
- **12, 13 PASS (math).** `twSteps` is a right-nested `∧` of `STStep2ConclgL` and the three `PrecL` conjuncts in both the definition and the check shape, so `Iff.rfl` is expected; the probe decides.
  Instance (13): `sz0` of (ii) for the band; BA at statement level with F3-F5, F7 open.
- **Registry (premise scan):** `STStep2DecayPTgL` (target 5), `STGdecayWgL` (target 6), `STDecaygL` (target 9, (E2)) are hypotheses of public theorems here, so the three unregistered merged pins
  are added with the expected `STKcalDecaygL`, `STScaleInvgL`, `STGoodAtg`. New hypothesis predicates F4 (Ward pair) and F7 (rotation) are model-free; F4 is proved at BA by T7-BA, F7 by T1-BA.

**Overall verdict: PASS** (targets 1-6, 8-13; target 7 moves to U2). Paper-delta candidates: `T2454a`: F4 and F7 are made explicit carrier hypotheses (the paper uses them implicitly via the Ward identity and trace cyclicity).

## (a′) Preflight corrections — Mon Oct 12 13:58:11 UTC 2026

Found by the probe step; the verdict of (a) is unchanged (evidence and scripts in (a″)).
- **C1. Table (ii) omits the grid fact F9.** The generic events need `S2EvGen_Grid Cm μ` (probe :191): `∃ Hm` with `Cm.GMM`, `Cm.LM` at `Hm` equal to `G − M`, `L`, both measurable in the matrix, and the transfer
  `Cm.Pp {Hpath ∈ S} = μ {Hm(gridTime) ∈ S}` (`Step2Core.lean:400`). Reason: the band lemmas under (E1)-(E4) name `sz.Prec`, `pathP sz`, `sz.seqHflow` in their statements (`Step2Events.lean:50,61,77,101-103,124-126`;
  `Step2Core.lean:430-434`; the proof of `ST_whp_grid` calls `ST_pathP_eq_seqP` at :455), so `ST_prec_*`, `ST_grid_whp_*`, `ST_whp_grid`, `ST_PT_of_sections` are not "model-free, reused" (ticket item 11) and need generic copies (up to 158 band lines). F9 is a hypothesis predicate, not a field;
  proved at the band (`bandStep2_Grid` :311) and at BA (`baStep2_Grid` :317, 8 lines). F3 also enters (E3), (E4) (`eta > 0`), not (E1), (E2), `ST_good_probg`, `ST_LW_sectionsg`.
- **C2. F4 at BA.** The Hermitian source is the public `EMn2BA_seqHflowBA_herm` (`BA/EMn2BA.lean:68`), not the private `ConArg_seqHflowBA_isHermitian`. F4 is proved at BA (`baFM_WardPair` :133), F3 (:384) and F1-F2
  (`baFlow_facts` :329) too: T7-BA's open inputs for targets 4-6 reduce to F5 (U2-BA), F6 (target 5) and the Step 2 decay.
- **C3 (1b, Mon Oct 12 15:46:47 UTC 2026). `ST_mE_im_ge` is not importable into `Chain/DecayGen`.** (a″) R3 and probe :114 read `ST_mE_im_ge` (`Step2Events.lean`) for F3 at the band; `Chain/DecayGen` imports `Induction/DecayLoopB`, whose closure does not contain `Induction/Step2Events` (script in (b)). `DecayGen_bandSpec` therefore uses the private `DecayLoopB_mE_im_ge` (`DecayLoopB.lean:1108`, the same bound `√κ/2 ≤ Im m` for `|E| ≤ 2 - κ`) by `open private`: 12 private names in all. No verdict changes; T7b may reuse `DecayGen_bandSpec`.

## (a″) Probe compile — Mon Oct 12 13:58:11 UTC 2026 (condensed by the 1b to keep the report within CLAUDE.md §6's 300 lines)

The uncondensed (a″) and (a‴), with the probe's line map and the script outputs, were read by the 1a-audit, whose report re-runs the scripts and quotes their output
(`docs/reports/T2454-1a-audit.md` §1-§9); the probe is `RBM3D/Probe/T2454Pins.lean` at `e949c71`.
- `RBM3D/Probe/T2454Pins.lean` on `t/T2454`, commit `e949c71`, 397 lines (limit 400), never merged, no root import; base `4fad610`. `lake env lean` of it, 13:54:37 to 13:54:42 UTC: exit=0, 28 output lines, 0 `error|warning`, 0 `sorry|admit|native_decide|axiom`. It states targets 1-6, 8-12 as the `Prop`s `T2454_<name>` and their instances.
- R1 `Iff.rfl`: fails for target 1 (binder swap); compiled for targets 2, 8, 11 and TLF-C5 (`twSteps`). `STGoodAt`, (E3), (E4) read `(mE E).im * (1 - u)` against `etaT E t := (1 - t) * (mE E).im` (`mul_comm`): proved bridges in T7b.
- R2 band declarations to copy 1,433 lines + probe 193 + 74 + 53 = 1,753 before extra instances. R3 `open private` compiled at the head of the probe (the 1b's list: (b)). R4 `hyprules.py`: no forbidden token in the 28 probe statements (the five band readings contain them, allowed).
- R5 registry preview: unregistered premises `STStep2DecayPTgL`, `STGdecayWgL`, `STDecaygL`, `LWtermG`, `LWtermExpG`, `S2EvGen_Sect`; superseded by (a‴) item 4.
- Paper-delta candidates (R4): `T2454b` F9 explicit (T7b); `T2454c` `|E| ≤ 2 - κ` replaced by `DecayGen_Spec` (`κm = √κ/2` at the band, `κ` at BA) and the energy-free `STKcalDecaygL`; `T2454d` target 6 drops the unused `s ≤ t` and `ε`, target 5 takes F6 (`N⁻¹ ≤ 1 - t`) in place of the range of `STFlow`.

## (a‴) 1a resubmission (H248) — Mon Oct 12 15:18:31 UTC 2026 (condensed by the 1b; script outputs verbatim in `T2454-1a-audit.md` §3-§6)

- Item 1 (`central.py`, re-run by the 1a-audit with identical output): predicted DecayGen 820, DecayGenTw 63, Step2EventsGen 1038, Step2EventsGenTw* 58, registry 8 lines; unsplit central 1962 > 1950, so the split applies (sensitivity 1,727 to 2,102):
  T7a = DecayGen + DecayGenTw + 3 registry lines = 886; T7b = Step2EventsGen + Step2EventsGenTw* + 5 registry lines = 1,101. Confirmed at 1a-audit round 2 (§3, §9); this 1b delivers T7a only. The two T7a lines of `central.py`, verbatim:
  `  DecayGen            820 = header 40 + pins[p] 60 + stmts4-6[p] 20 + bridges[p] 45 + proofs4-6[b] 622 + inst4-6[p] 33`
  `  DecayGenTw           63 = header 30 + TLF-C5[p] 14 + BAward+BAinst6[p] 19`
- Item 2 (`layout.py`): `Chain.DecayGen` imports `Induction.DecayLoopB`, `Chain.Step2Gen` (closure 86 modules, 0 `BA/` modules, importer `Chain.DecayGenTw` only); `Chain.DecayGenTw` imports `Chain.DecayGen`, `BA.TwistPins`, `BA.Step2BA`, `BA.EMn2BA` (closure 273 modules, 29 `BA/`, no importer).
- Item 3 (`readers2.py`): 51 public declarations of `Step2Events`/`Step2Core` read by `Step2Iterate`/`OptL2a`/`OptL2b`: 30 model-free and reused, 20 generic forms in T7b, `ST_good_engine` is T1's P4 (`T2452-design.md:184`), 0 unclassified. None belongs to T7a.
- Item 4 (`registry.py`): 8 `owedProps` lines in all; T7a adds `STKcalDecaygL`, `STStep2DecayPTgL`, `STGdecayWgL`; T7b adds `STScaleInvgL`, `STGoodAtg`, `STDecaygL`, `LWtermG`, `LWtermExpG` (`STStep1WeakgL` is registered).
- Verdict: targets 1-6, 8-13 PASS; target 7 deferred to U2 (no `Chain/Step34Gen` on `main`).

## (b) Script output (1b; T7a = `RBM3D/Chain/DecayGen.lean`, `RBM3D/Chain/DecayGenTw.lean`, 3 lines in `RBM3D/Test/Axioms.lean`)

Branch `t/T2454`: `02f19f2` (DecayGen, `date -u` 15:34:52 UTC), `6affbeb` (DecayGenTw and the registry lines, 15:39:11 UTC). The 1b's first `date -u` was Mon Oct 12 15:23:33 UTC 2026. Probe, 1a-audit and (a)-(a‴) are as above.
```
$ lake build RBM3D.Chain.DecayGen RBM3D.Chain.DecayGenTw | tail -1          # 15:42:26 UTC
Build completed successfully (4012 jobs).
$ date -u; lake build; echo exit=$?; date -u      # whole library; RBM3D.lean + 2 temporary import lines for the new modules (uncommitted, reverted: the hub adds root imports)
Mon Oct 12 15:39:38 UTC 2026 ... exit=0 ... Mon Oct 12 15:40:21 UTC 2026
info: RBM3D.lean:515:0: axiom audit: 13299 theorems, 4175 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.STKcalDecaygL: 4 [no certificate]   RBM.BA.STStep2DecayPTgL: 2 [no certificate]   RBM.BA.STGdecayWgL: 2 [no certificate]
Build completed successfully (4283 jobs).
$ lake env lean axioms.lean     # #print axioms of the ten new public theorems (DecayGen_Spec, DecayGen_WardPair and the pins are defs)

'RBM.BA.bandFM_STDecayLoopU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STDecayLoopPT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STKcalDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.DecayGen_bandSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.DecayGen_ward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.DecayGen_bandWardPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stDecayLoopAtgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stDecayLoopPTgL_of_step2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stDecayLoopUgL_of_step2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.DecayGenTw_baWardPair' depends on axioms: [propext, Classical.choice, Quot.sound]
$ wc -l RBM3D/Chain/DecayGen.lean RBM3D/Chain/DecayGenTw.lean         # stop line 2,000 per file; 1a predicted 820 and 63
 657 RBM3D/Chain/DecayGen.lean    80 RBM3D/Chain/DecayGenTw.lean       (T7a total 657 + 80 + 4 registry lines = 741, predicted 886)
$ python3 -I stmts_final.py RBM3D/Chain/DecayGen.lean                 # statements of targets 4-6 extracted from the file (pins 1-4: `def` lines 66, 73, 83, 105)
theorem stDecayLoopAtgL_of {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ)
    (hW : DecayGen_WardPair C) (hK : STKcalDecaygL C) (κm 𝔠 𝔡 C₀ : ℝ) (u P : ℕ → ℝ) :
    STDecayLoopAtgL C μ κm 𝔠 𝔡 C₀ u P
theorem stDecayLoopPTgL_of_step2 {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (κm 𝔠 𝔡 : ℝ)
    (s t : ℕ → ℝ) (Cd : ℝ) (hspec : DecayGen_Spec C κm) (hA : sz.Admissible 𝔠 𝔡) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hrange : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n) (hW : DecayGen_WardPair C)
    (hK : STKcalDecaygL C) (hD : STStep2DecayPTgL C μ Cd s t) : STDecayLoopPTgL C μ s t
theorem stDecayLoopUgL_of_step2 {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (κm 𝔠 𝔡 : ℝ)
    (s t : ℕ → ℝ) (Cd : ℝ) (hspec : DecayGen_Spec C κm) (hA : sz.Admissible 𝔠 𝔡) (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hW : DecayGen_WardPair C) (hK : STKcalDecaygL C) (hD : STGdecayWgL C μ s t Cd) : STDecayLoopUgL C μ s t
```

Hypothesis table as finally used (T7a theorems 4 / 5 / 6; every line C1-clean and spectral-clean: no `‖m‖ = 1`, scalar `m`, `mE`, `zt`, `etaT`, `STFlow`, `lemT`, `pathP/H`, `SB`):
- F1 `sz.Admissible 𝔠 𝔡` (`hA`): 4, 5, 6. Band `.1` of `STFlow` (`sz0_admissible` in the instance); BA `h.1` of `BAFlow`.  F2 `0 ≤ s`, `t < 1` (`hs`, `ht1`; target 4: `0 ≤ u n`, `u n < 1`): band `lemT_lt_one`; BA `EMn2BA_T0_lt_one`.
- F3 `DecayGen_Spec C κm`: 4, 5, 6. Band `DecayGen_bandSpec`; BA `EMn2BA_mF_data`.  F4 `DecayGen_WardPair C`: 4, 5, 6. Band `DecayGen_bandWardPair`; BA `DecayGenTw_baWardPair`.
- F5 `STKcalDecaygL C`: 4, 5, 6. Band `bandFM_STKcalDecay`; BA U2-BA `BAKcalDecay` (owed, DECISIONS §264).  F6 `∀ᶠ n, N⁻¹ ≤ 1 - t n` (`hrange`): target 5 only. Band instance `DecayGen_inst_hN`; BA `EMn2BA.lean:111`, `TwistLoop.lean:88` (T7-BA).
- Step 2 decay (hypotheses, other gates): `STStep2DecayPTgL` (5), `STGdecayWgL` (6), the decay input of the `(+,-)` 2-loops (4): T1 / T1-BA.  Placement: target 7 is U2's (no `Chain/Step34Gen` on `main`); target 11 (L-bridges) is T7b's.

```
$ lake env lean stmtcheck.lean     # `example : T2454_x := @x` for the probe Props of targets 4, 5, 6 (probe :85-98, copied verbatim): exit=0, `grep -c error` = 0
$ lake env lean pincheck.lean      # check-file bodies: `STDecayLoopUgL C μ s t ↔ T2454_DecayLoopUgL C μ s t := Iff.rfl`; `STKcalDecaygL C ↔ T2454_KcalDecaygL C := Iff.rfl`;
                                   # `h.2.2.2 : T2454_DecayLoopUgL` from `twSteps`; `bandFM_STDecayLoopU`, `bandFM_STKcalDecay` at the check-file shapes: exit=0, `grep -c error` = 0   (scratch files `stmtcheck.lean`, `pincheck.lean`, `axioms.lean` in `scratchpad/T2454/`, not committed)
$ grep -n "^example" RBM3D/Chain/DecayGen.lean RBM3D/Chain/DecayGenTw.lean | cut -c1-90        # the compiled nonempty instances
DecayGen.lean:619 target 6 at the band carrier (`d = 3`, `sz0`, `z0`, `flow_z0`, `[s,t] = [0,1/16]`), via `bandFM_STDecayLoopU`; open: `STGdecayWgL`
DecayGen.lean:627 target 5 at the band (F6 `N⁻¹ ≤ 1 - t` discharged by `DecayGen_inst_hN`); open: `STStep2DecayPTgL`
DecayGen.lean:637 target 4 at the band (`E ≡ 0`, `u ≡ 1/2`, `P ≡ 1`, `C₀ = 0`, `k = 3`, `τ' = 1/10`, `D' = 1`); open: the decay input of the `(+,-)` 2-loops
DecayGenTw.lean:54, :63 target 12: `twSteps … ↔ (STStep2ConclgL … ∧ conjunct 2 ∧ conjunct 3 ∧ STDecayLoopUgL …) := Iff.rfl`; `h.2.2.2`
DecayGenTw.lean:71 target 6 at the BA carrier `baFMz sz z`, law `seqP (sz.withLam 0)` (statement level, target 13); open: `STKcalDecaygL` (U2-BA) and `STGdecayWgL` (T1-BA)
$ python3 -I closure.py          # import closure of the new modules, from the `import RBM3D.` lines of the branch
RBM3D.Chain.DecayGen closure 86 modules; BA modules: 0 ; contains Induction.Step2Events: False
RBM3D.Chain.DecayGenTw closure 273 modules; BA modules: 29 ; contains Induction.Step2Events: True
$ grep -n '^import RBM3D.BA' RBM3D/Chain/DecayGen.lean ; grep -rln "import RBM3D.Chain.DecayGen" RBM3D RBM3D.lean       # (no output) ; reverse cone
RBM3D/Chain/DecayGenTw.lean
$ git diff main...t/T2454 --stat | cat ; git diff main...t/T2454 -- RBM3D/Induction/ | wc -l          # main = ab5746d; the probe is never merged
 RBM3D/Chain/DecayGen.lean   | 657 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/DecayGenTw.lean |  80 ++++++
 RBM3D/Probe/T2454Pins.lean  | 397 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |   4 +
 4 files changed, 1138 insertions(+)
       0
$ bash clash2.sh     # whole-word grep of the new public names in `RBM3D/`, `RBM3D.lean` (branch; Probe/ and the two new files excluded) and `git grep -nw` on `main`
16 new public names; occurrences elsewhere: branch 7, main ab5746d: 0      # the 7 are my registry comments at `Test/Axioms.lean:199-201`
$ grep -cE 'sorry|admit|native_decide|\baxiom\b' RBM3D/Chain/DecayGen.lean RBM3D/Chain/DecayGenTw.lean       # 0 and 0
$ python3 -I hyprules_final.py     # tokens `mE zt etaT STFlow lemT pathP pathH SB ‖m‖ |E Lloop STKloop seqHflow`
16 public declarations scanned (theorem statements, def bodies); forbidden tokens in: [('bandFM_STKcalDecay', ['|E']), ('DecayGen_bandSpec', ['|E'])]     # band readings: allowed
```

**`open private` (12 names, `Induction/DecayLoopB.lean`; precedent `Chain/NewKLKGen.lean:32-43`).** `DecayLoopB_pair` (Ward pair, F4), `_alg` (the exponent chain), `_exp_small`, `_real_geom`, `_one_sub_u`, `_STWB_le`, `_STWB_nonneg`, `_two_mul_diam_le`,
`_diam_le_KLmaxDist`, `_zdistD_le_KLmaxDist_two`, `_diam_one`, `_mE_im_ge`. Each is used (2 to 6 occurrences in `DecayGen.lean`); their statements name `Zd`, `STWB`, `loopL`, reals only; copying them is the helper block `DecayLoopB.lean:802-1377`. Band files unedited (G1 not applicable).

**Narrative.**
- Layout (A), additive, T7a: `DecayGen` (targets 1-6, band instances), leaf `DecayGenTw` (F4 at BA, TLF-C5, BA instance of target 6). No existing module imports either; root imports are the hub's (precedent: `t/T2458` commit `a3d9518` touches only the module, the merge commit `1debc23` adds the root import). Target 7 (`stEtermDecay`) is U2's: no `Chain/Step34Gen` on `main`.
- Proof structure: the pointwise chain common to `DecayLoopA_main` and `DecayLoopB_main_u` is one private lemma `DecayGen_step` (index `n`, time `u`, labels, Ward pair `c`, the complement of the one bad event). `DecayGen_main_at` (per time, `perTimeCalc_of_imp`) and `DecayGen_main_u` (uniform, `StochDomAt.of_subset`) are
  thin wrappers; target 5 reuses target 4 through `perTime_timeIcc_of_forall_seq`/`perSeq_of_perTime_timeIcc`. The band's prefactor bound `P_u ≤ N^{max Cd 0 + 1}` is `DecayGen_prefactor` (`Bctl ≤ 2`, `(1-s)/(1-v) ≤ N`). `DecayGen` has 657 lines against the 1a's 820 (the shared step); `DecayGenTw` 80 against 63.
- Carrier hypotheses (`DecayGen_Spec`: `0 < κm ≤ Im m`, `η_t = (1-t) Im m`; `DecayGen_WardPair`; `STKcalDecaygL`) replace `0 < κ`, `|E n| ≤ 2 - κ`, `etaT`, `zt`, `Lloop`; `Γ = κm⁻¹` (band `2/√κ`, BA `1/κ`). `1 - u ≥ N⁻¹` is derived from the far premise (targets 4, 6) or is the hypothesis F6 (target 5).
- Statement shapes: targets 4-6 equal the probe `Prop`s (`example : T2454_x := @x`); target 1 and 3 bodies equal the check file's (`Iff.rfl`); target 1's band bridge is a binder swap (`bandFM_STDecayLoopU`, proved, not `Iff.rfl`); target 2's is `Iff.rfl`.
- F3 and F4 are proved at the band (`DecayGen_bandSpec`, `DecayGen_bandWardPair`) and F4 at BA (`DecayGenTw_baWardPair`); F3 at BA is `EMn2BA_mF_data` (in the instance at `DecayGenTw.lean:71`). Open at BA: F5 (`BAKcalDecay`, U2-BA), the Step 2 decay (T1-BA), F6 for target 5 (T7-BA).
- Registry: `STKcalDecaygL`, `STStep2DecayPTgL`, `STGdecayWgL` added to `owedProps` (3 lines + 1 comment line); `DecayGen_Spec`, `DecayGen_WardPair` are concluded by `DecayGen_bandSpec`, `DecayGen_bandWardPair`, so the scan does not list them. The full build above runs `#assert_rbm_axioms`: passes.
- `lem_decayLoop` for `k = 1` is empty (`diam_∞ a = 0 < ℓ_u W^{τ'}`): `DecayGen_one_ind`; `k ≥ 2` follows paper `3_5:1126` through the adjacent-pair cut in `DecayLoopB_pair`.
- No new `FlowFM`/`Step2Mat` field, no `Step2Data`, no `STFlow`/`lemT` in any generic statement; in targets 4-6 `hd : 3 ≤ d` is used only for `2 ≤ d` (`bandFM_STKcalDecay` uses `3 ≤ d`).
- No port from `../RBM1D` or `../RBM2D`: the copied proof text is RBM3D's `DecayLoopA.lean:713-922` (`DecayLoopA_main`), `:970-1082`, `DecayLoopB.lean:1386-1623` (`DecayLoopB_main_u`), `:1637-1664`, adapted from the band to the carrier (last commits `6179d8c`, `250a118`).

## (c) Verified Mathlib names (each `#check @name` in `scratchpad/T2454/mathlib_check.lean`, exit 0, 0 errors)

`Real.exp_pos`, `Real.one_le_rpow`, `Real.rpow_add`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_mul`, `Real.rpow_nonneg`, `Real.rpow_one`, `Real.rpow_pos_of_pos`, `Real.sqrt_eq_rpow`, `Real.sqrt_pos`, `Real.exp`, `Real.sqrt`;
`inv_anti₀`, `inv_inv`, `mul_inv_cancel₀`, `mul_one_div_cancel`, `le_div_iff₀`, `div_le_iff₀`, `le_mul_of_one_le_left`, `le_mul_of_one_le_right`, `mul_le_mul`, `mul_le_mul_of_nonneg_left`, `le_abs_self`, `norm_sub_le`, `norm_le_norm_add_norm_sub'`;
`tendsto_rpow_atTop`, `tendsto_natCast_atTop_iff`, `Filter.tendsto_atTop_mono'`, `Filter.Tendsto.eventually_ge_atTop`, `Filter.Eventually.of_forall`, `Nat.lt_or_ge`, `Nat.cast_nonneg`, `List.ofFn_succ`. Verified absent: none needed.

## (d) Open issues and paper-delta candidates

- T7b (dispatcher): `Chain/Step2EventsGen` (targets 8-11) with the events part of the BA readings; the 1a-audit observations O1 (a 4th file is not needed: `DecayGenTw` may import `Chain/Step2EventsGen` after T7a merges) and O2 (`Step2EventsGen_Sect` as a `Prop` premise needs unbundling or a registry line); T7b adds `STScaleInvgL`, `STGoodAtg`, `STDecaygL`, `LWtermG`, `LWtermExpG`.
- Target 7 (`stEtermDecay`) is U2's; U2 supplies the `TimeIcc`-uniform `STKboundgL`. U2 / U2-BA own `STKcalDecaygL` (`BAKcalDecay`); T1 / T1-BA own `STGdecayWgL`, `STStep2DecayPTgL`; T7-BA proves target 6 at BA from `DecayGenTw.lean:71` once those are available.
- Root imports `import RBM3D.Chain.DecayGen` and `import RBM3D.Chain.DecayGenTw` are for the hub (hub rule A step 4); the full build above was run with them in the working tree.
- Paper-delta candidates: `T2454a`-`d` as in (a), (a″) (F4 and F7 explicit; F9 explicit; `|E| ≤ 2 - κ` replaced by `DecayGen_Spec`; target 5 takes F6, target 6 drops `s ≤ t`, `ε`). No further Lean/paper statement difference in T7a.

