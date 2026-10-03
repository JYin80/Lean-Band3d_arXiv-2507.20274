Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 06:37:36 UTC 2026

Notation: `x=1−t`, `g=ilambda`, `Δ_t=W^{-d}B_{t,0}`, `r=(1−s)/(1−t)`, `B_{t,K}=(g²+x)^{-1}(K+1)^{2−d}+(L^d x)^{-1}` (1_2:1107, merged `Bparam`), `ℓ_t=min(max(g x^{-1/2},1),L)` (1_2:1121), `tr`=unnormalised trace, `E_a=W^{-d}1_{[a]}` (1_2:81). Sequence `sz0`, n=0 (`RBM3D/Defs/Sizes.lean:260`): d=3, L=4, W=32, g=1/64, N=(WL)^d=2^21.

### (i) Exponent table (values at sz0 n=0; "derived" = my algebra from the displayed paper inequalities, checked in `inst.py`)
| quantity | value | constraint (source) | slack |
|---|---|---|---|
| d, L | 3, 4 | d≥3, L≥3 | 0, 1 |
| 𝔡 (eq:WO, 1_2:363) | 0.1 | W^{-d/2+𝔡}≤g≤𝔡^{-1} | 0.0078≤0.0156≤10 (×2 low side) |
| 𝔠 (Main_DEL_COND) | 1/6 | W≥N^𝔠 | N^𝔠=11.31≤32 (×2.8) |
| ε (η_t≥N^{-1+ε}, 1_2:807) | 0.1 | N(1−t)≥N^ε | 209.7≥4.29 at 1−t=1e-4 |
| Δ_t upper (derived) | 0.0934 | Δ_t≤(g²W^d)^{-1}+(Nx)^{-1}≤W^{-2𝔡}+N^{-ε} | 0.125+0.233 worst (1−t=N^{-1+ε}); →0 along sz0 (limits below) |
| regime R1 x≥g² | ℓ=1; B_{t,K}≍x^{-1}(K+1)^{2−d}; Δ=6.2e-5 at x=.5 | zero-mode term dominated for K≤L (3_5:325) | first 2.0 vs zero 0.031 |
| R2 g²/L²≤x≤g² | ℓ=g x^{-1/2}=1.56; B_{t,0}≍g^{-2}; Δ=0.0935 at x=1e-4 | 1≤ℓ≤L | 1.56∈[1,4] |
| R3 g²/L^d≤x≤g²/L² | ℓ=L=4; B_{t,0}≍g^{-2} (derived: g²+x∈[g²,2g²], (L^d x)^{-1}≤g^{-2}); Δ=0.18 at x=8e-6 | exp factor e^{-(r/ℓ)^{1/2}} of constant order (3_5:325) | first 3966 vs zero 1953 |
| R4 x<g²/L^d (derived; needed) | B_{t,0}≍(L^d x)^{-1}; Δ=0.28 at x=3e-6 | admissible iff x≥N^{-1+ε}; n=0: N^{-1+ε}=2.04e-6<g²/L^d=3.8e-6, so R4 is inside the Step-2 range | zero 5208 vs first 4046 |
| Step-1 weak LL exponent (1_2:1328) | 1/4 | Gtmwc: ‖G−M‖_max≺Δ^{1/4} | — |
| output exponent (Eq:Gdecay_w, 1_2:1350) | 1/5 | 1/6<1/5<1/4 (1_2:1353 text "less than 1/4") | gap to stop 1/30 |
| stopping exponent (eq:def2_stopping, 3_5:533) | 1/6 | J^{3/2}≤Δ^{(1/6)(3/2)}=Δ^{1/4} closes (eq:boundmgterm, 3_5:542) | 0 (equality, J≤Δ^{1/6} by def. of T) |
| martingale exponents (eq:MG_conclusion3) | Δ^{1/2}+J³ → sqrt → Δ^{1/4}+J^{3/2} | J³≤Δ^{1/2} iff J≤Δ^{1/6} | 0 |
| C_0 = C_d (Eq:Gdecay_w) | 10 (instance value, NOT from the paper) | depends only on c_d, C_d of prop:ThfadC; independent of 𝔠_d | paper gives no numeral |
| 𝔠_d (con_st_ind, 1_2:1296) | 1/400 | (a) L-K2max: 𝔠_d(C_0+5/4)<1/4 (3_5:481–510); (b) Gronwall<stop at u=t: 𝔠_dC_0<1/5−1/6=1/30; (c) all u∈[s,t] (derived: Δ_t≤Δ_u(1−u)/(1−t), r_u≤r_t): 𝔠_d(C_0+1/6)<1/30 i.e. 𝔠_d<1/(30C_0+5); paper cap 1e-2 | 1/400 vs 1/305=3.28e-3 (×1.31); (a) 1/45 |
| window (1−t)/(1−s) | [Δ_t^{𝔠_d},1)=[0.99409,1), r=1.0025 | Δ_t^{𝔠_d}≤1/r<1 | nonempty, width 5.9e-3 |
| Gronwall factor r^{C_0} (eq:Gronwall_dervJuD) | 1.025 | r_u^{C_0}Δ_t^{1/5}<Δ_u^{1/6} ∀u∈[s,t] | min_u gap 0.0354 (scan) |
| ℓ'-iteration (eq:def_ell1) | T_u(K')=T_u(K)Δ_u^{1/6}; K=47 (D=3), 109 (D=10) | B_{u,0}Δ^{k/6}≤W^{-D}: k≥6(D ln W+ln B)/(−ln Δ)=O(1) | finite, D-dependent only |
| ℓ ≤ (log W)^{10}ℓ_t (EWGn2_N) | ℓ≤L=4 vs 3.9e5 | | huge |
| LW window (initialGT2 3_5:28, Ψ_t=Δ^{1/2}, ε_0=0.1) | W^{-3/2}=0.0055≤0.306≤W^{-ε_0}=0.707 | W^{-d/2}≤Ψ_t≤W^{-ε_0} | ok |
| N-scale of every W^τ (D23) | W^τ≤N^{τ/d} (`Sizes.W_rpow_le`); N^τ≤W^{τ/𝔠} (`Sizes.size_rpow_le_W_rpow`); W^{-c}≤N^{-𝔠c}; W^{-D}≤N^{-𝔠D} (D arbitrary) | τ≥0 | W=32≤128; N=2^21≤W^6=2^30 |
| d=2 tokens (`git show c9a24cf:RBM2D/Path/Scales.lean`) | :41 `ellT=min(1/√(1−u),L)` (no g); :44 `scaleM=W²ℓ²η`; :115 `scaleM=W²Im m·min(1,L²(1−u))`; :197 hypothesis `(scaleM)⁻¹≤((1−t)/(1−s))^30` | d=3: scaleM⁻¹ becomes `Δ_u` (g-dependent ℓ_u, extra regimes R2–R4); d=2,g=1: B_{u,0}/max(1,1/(L²(1−u)))∈[1/2,2] | 30 matches 1/30 of (b) (lead only) |

### (ii) One concrete nondegenerate instance
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/inst.py` (sequence, constants, window, Gronwall/stopping scan, limits). All deterministic hypotheses of Step 2 and of the LW inputs hold at once: d=3, N=2^21, 1−t=1e-4, 1−s=1.0025e-4, nothing collapsed. External hypotheses (Step 1 conclusions, LW lemmas: stochastic, owed to ST-1 / LW gates): concrete limit along sz0 below (worst 1−t=N^{-1+ε}); Δ_t→0, so every `≺` hypothesis is nonvacuous and the factor-`Δ` gains (Δ^{1/4}, Δ^{1/5}, Δ^{1/6}) are strict improvements.
```
d,L,W,g,N = 3 4 32 0.015625 2097152
WO:  W^(-d/2+dd)=0.0078125 <= g=0.015625 <= 1/dd=10 : True
Bandwidth: N^c=11.314 <= W=32 : True
g^2=0.0002441  g^2/L^2=1.526e-05  g^2/L^d=3.815e-06  N^(-1+eps)=2.044e-06
c_d bounds: 1/(30C0+5)=0.0032787 (derived), 1/(4C0+5)=0.022222, 1/(30C0)=0.0033333, paper cap 1e-2; chosen c_d=0.0025 ok=True
regime  1-t        ell_t   B_t0       W^-d B_t0   [first, zero-mode term of B_t0]   dominant
R1 1-t>=g^2      0.5       1       2.03       6.196e-05   [1.999, 0.03125]  first
R2 g2/L2..g2     0.0001    1.562   3062       0.09345     [2906, 156.2]  first
R3 g2/Ld..g2/L2  8e-06     4       5919       0.1806      [3966, 1953]  first
below g2/Ld      3e-06     4       9255       0.2824      [4046, 5208]  zero-mode
t: 1-t=0.0001  Delta_t=0.093446  window (1-t)/(1-s) in [0.994092,1) nonempty: True
choose r=(1-s)/(1-t)=1.002506<=Delta^-c_d=1.005944: True ; 1-s=0.000100251 in (0,1]: True
Delta_s=0.09337 <= Delta_t=0.093446: True ; Delta_t/Delta_u<=(1-u)/(1-t) check at u=s: 1.0008 <= 1.0025
Gronwall: r^C0 Delta_t^(1/5)=0.63824  vs stopping Delta_u^(1/6)>=0.67364 (u=s: 0.67355)  strict: True
(1/6)(3/2)=1/4 ; J^3 <= Delta^(1/2) at J=Delta^(1/6): equality; Delta^(1/4)=0.55289
5/4 step: r^(C0+5/4) Delta^(5/4)=0.053141 << Delta=0.093446: True
D=3 iterations K needed: 47  (O(1), depends on D,Delta only)
D=10 iterations K needed: 109  (O(1), depends on D,Delta only)
W^tau<=N^(tau/d): tau=1  W=32, N^(1/3)=128 ok=True ; N^tau<=W^(tau/c): tau=1 N=2097152 <= W^6=1073741824 : True
(g^2 W^d)^-1=0.125 <= W^(-2dd)=0.5: True
Delta_worst over 1-t>=N^(-1+eps): (g2W^d)^-1+N^-eps=0.35826
LW: W^-1.5=0.0055243 <= Psi=0.30569 <= W^-e0=0.70711 : True ; ell_t=1.562 <= (log W)^10 ell_t=3.906e+05
limit along sz0 (worst 1-t=N^(-1+eps)):  n  (g2 W^d)^-1  N^-eps  sum
     0  0.125  0.2333  0.3583
     1  0.01562  0.06699  0.08261
     3  0.001953  0.01924  0.02119
     9  0.000125  0.003697  0.003822
    99  1.25e-07  5.859e-05  5.872e-05
   999  1.25e-10  9.286e-07  9.287e-07
d=2,g=1,L=4,1-u=0.5: B_u0=0.7917 vs max(1,1/(L^2(1-u)))=1 ratio 0.792 in [1/2,2]
d=2,g=1,L=4,1-u=0.01: B_u0=7.24 vs max(1,1/(L^2(1-u)))=6.25 ratio 1.16 in [1/2,2]
d=2,g=1,L=4,1-u=0.0001: B_u0=626 vs max(1,1/(L^2(1-u)))=625 ratio 1 in [1/2,2]
scan u in [s,t]: min_u [Delta_u^(1/6) - r_u^C0 Delta_t^(1/5)] = 0.0354 > 0: True
N(1-t)=209.7 >= N^eps=4.287: True
```
Numeric check of the two Step-2 local laws at d=3, W=2, L=3 (N=216), g=1/2, E=0 (m=i, z_u=i(1−u), H_u=√u·H, H_xy~N_R/N_C(0,W^{-d}S^B), 300 samples; |x−y|_L = periodic ℓ¹ on Z_6^3; ratios are O(1) constants, `≺` has no explicit constant at N=216). Command: `python3 .../scratchpad/mat.py`:
```
N=216  max|row sum S -1|=0.00e+00
u-regimes: g^2=0.25, g^2/L^2=0.02778, g^2/L^d=0.009259
regime 1-u>=g^2               1-u=0.5  eta_u=0.5  W^-d B_{u,0}=0.1759
   |x-y|_L : [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
   mean|(G-M)_xy|^2 / (W^-d B_{u,|x-y|/W}) : [0.201 0.194 0.147 0.098 0.06  0.032 0.018 0.013 0.009 0.01 ]
   max over samples/entries  same ratio    : [2.68 2.67 3.39 3.79 2.18 2.48 0.61 0.47 0.14 0.14]
   max_a|tr((G-M)E_a)| mean over samples = 0.1277 ; / (W^-d B_u0) = 0.726
regime g^2/L^2<=1-u<=g^2      1-u=0.1  eta_u=0.1  W^-d B_{u,0}=0.4034
   |x-y|_L : [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
   mean|(G-M)_xy|^2 / (W^-d B_{u,|x-y|/W}) : [0.312 0.33  0.306 0.274 0.246 0.226 0.217 0.214 0.216 0.229]
   max over samples/entries  same ratio    : [4.23 5.4  6.88 8.86 6.28 8.37 5.23 4.47 4.02 2.82]
   max_a|tr((G-M)E_a)| mean over samples = 0.2519 ; / (W^-d B_u0) = 0.624
regime g^2/L^d<=1-u<=g^2/L^2  1-u=0.02  eta_u=0.02  W^-d B_{u,0}=0.6944
   |x-y|_L : [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
   mean|(G-M)_xy|^2 / (W^-d B_{u,|x-y|/W}) : [0.503 0.534 0.559 0.57  0.579 0.588 0.6   0.611 0.624 0.643]
   max over samples/entries  same ratio    : [17.13 21.82 18.16 16.57 16.84 16.57 15.38 21.58 15.72 12.11]
   max_a|tr((G-M)E_a)| mean over samples = 0.4882 ; / (W^-d B_u0) = 0.703
```
Reading: mean |(G_u−M)_xy|²/(W^{-d}B_{u,|x−y|/W}) ≤ 0.64 and max over all samples and entries ≤ 21.8 in all three regimes (no blow-up as u→1 inside g²/L^d≤1−u); max_a|tr((G_u−M)E_a)|/(W^{-d}B_{u,0}) ≈ 0.62–0.73. Both bounds hold as O(1) ratios.

### Verdict per target (math preflight)
- Step 2 pins (Gt_bound_flow, Gt_avgbound_flow, Eq:Gdecay_w) and ingredients (lem:newKLK, EMn2_N, LWterm, EWGn2_N, stopping time, Gronwall): **PASS** — every exponent closes (1/6<1/5<1/4; J^{3/2}→Δ^{1/4} with zero slack; 𝔠_d<1/(30C_0+5)); the instance above satisfies all deterministic hypotheses.
- Findings for stage 1b: (1) the paper fixes no numeral for C_0, 𝔠_d: pins keep them as constants before the sequence with constraint 𝔠_d(C_0+1/6)<1/30 (derived, not paper); (2) regime R4 (x<g²/L^d, down to N^{-1+ε}) occurs inside the Step-2 range and needs no new pin only if all pins are stated through `Bparam` for every `x>0`; (3) `tr` is the unnormalised trace (assumed from `tr[G E_u]`, 1_2:92).

## (b) Script output — written Sat Oct  3 13:54:12 UTC 2026

Probe commit `509cf7d` on `t/T2039` (base `cca94be`); `git diff --stat main...t/T2039` (main at `37a8655`): 1 file, `RBM3D/Probe/T2039Pins.lean`, 5902 lines. Report-only ticket: the probe stays on the branch (never imported, never merged). Items 1, 3, 4, 6, 7 are in `docs/reports/T2039-portmap.md` (1562 lines: P.1 inventory, P.2 class-c rewrite rows, P.3 exponents, P.4 routes, P.5 split, P.6 Block Anderson, P.7 registry, P.8 findings F1–F16, P.10 the scripts of this report verbatim); the pins and instances extracted from the probe by script are its P.9, P.9b.

### b.1 Build and hygiene (`date -u`: 13:38:13 to 13:38:51 UTC)
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2039 && lake build RBM3D.Probe.T2039Pins; echo "exit $?"
info: RBM3D/Probe/T2039Pins.lean:5902:0: 'RBM.Gauss.Sizes.STgDrift_eq_STgDriftN' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3739 jobs).
lake build RBM3D.Probe.T2039Pins  81.21s user 9.65s system 235% cpu 38.576 total
exit 0
$ lake env lean RBM3D/Probe/T2039Pins.lean; echo "exit $?"      # exit 0; 15 `warning:` diagnostics (12 unused variable names, 3 deprecations), 0 `error`
$ grep -c 'sorry\|admit\|native_decide' RBM3D/Probe/T2039Pins.lean; grep -c '^axiom' RBM3D/Probe/T2039Pins.lean
0
0
```
### b.2 Axioms
```
$ lake env lean RBM3D/Probe/T2039Pins.lean | grep 'depends on axioms' | sed 's/.*depends on axioms: //' | sort | uniq -c
     31 [propext, Classical.choice, Quot.sound]
(31 = the 21 `inst_*`, ST_step2_of_pins, ST_step2_of_pinsN, ST_step2_concl, ST_concl_of_step2, ST_avgU_of_avg, ST_gridMart_of_repN, ST_Bdata_holds, STstopIdx_isStoppingTime, STEEM_eq_STeeM, STgDrift_eq_STgDriftN)
$ lake env lean axcheck.lean        # `import RBM3D.Probe.T2039Pins`; collectAxioms of every declaration of the module
checked 304 declarations of RBM3D.Probe.T2039Pins (195 theorems); declarations using an axiom outside [propext, Classical.choice, Quot.sound] (incl. sorryAx): []
```
### b.3 Targets: the three conclusions of Step 2 and the pin (`extract_stmt.py`, docstrings omitted; the other pins are in P.9)
```
-- STStep2Local (probe lines 457-460)
def STStep2Local (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖ ^ 2)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2)))
-- STStep2Avg (probe lines 464-467)
def STStep2Avg (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Zd d (sz.L n))
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) (fun _ : Fin 1 => true) (fun _ => p.2) ω - mE (E n)‖)
    (fun n p _ => sz.Bctl n (p.1 : ℝ))
-- STStep2Decay (probe lines 472-481)
def STStep2Decay (Cd : ℝ) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
-- STStep2 (probe lines 805-814)
def STStep2 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep1Loop sz (STflowE z) s t → STStep1Weak sz (STflowE z) s t →
            STStep2Local sz (STflowE z) s t ∧ STStep2Avg sz (STflowE z) s t ∧
              STStep2Decay sz Cd (STflowE z) s t
```
Pin index (probe lines at 509cf7d, `extract_stmt.py`): STStep2:805-814 STStep2Local:457-460 STStep2Avg:464-467 STStep2Decay:472-481 STNewKLK:586-587 STContractPt:600-609 STLWB:615-624 STLWT:630-645 STEMn2Poly:650-659 STEMn2Exp:665-682 STGridRepNAt:5119-5152 STGridRepN:5156-5156 STGridMart:746-746 STstopIdx:753-757 STK2decay:777-781 STNetLift2:790-797 STScaleExists:4106-4110 STOptL2:4117-4126 STLocalAvgOfL2:4144-4149 STStep2Concl:4784-4785 ST_step2_of_pins:4639-4641 ST_step2_of_pinsN:5341-5343 ST_step2_concl:4871-4879
### b.4 Compiled nonempty instances (`d = 3`, merged `sz0`, flow points `z0`, `s ≡ 0`, `t ≡ 1/16`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; all 21 are in P.9b)
```
inst_step2:5489 inst_step2_lowg:5503 inst_newKLK:5548 inst_contractPt:5576 inst_LWB:5632 inst_EMn2Poly:5644 inst_LWT:5667 inst_EMn2Exp:5679 inst_gridMart:5695 inst_stop:5719 inst_K2decay:5725 inst_netLift2:5739 inst_Bdata:5750 inst_scaleExists:5761 inst_optL2:5768 inst_localAvg:5783 inst_skeleton:5793 inst_step2_concl:5806 inst_skeleton_concl:5821 inst_gridRepN:5835 inst_skeletonN:5858
-- inst_step2 (probe lines 5489-5494)
theorem inst_step2 (h : STStep2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Local sz0 (STflowE z0) sInst tInst ∧ STStep2Avg sz0 (STflowE z0) sInst tInst ∧
          STStep2Decay sz0 Cd (STflowE z0) sInst tInst) := by
```
Discharged at the concrete data: `STFlow` (`flow_z0`), `0 ≤ s`, `s < t ≤ lemT z_n` (`sixteenth_le_lemT`), `STConStInd` for the `𝔠_d` the pin returns (`conStInd_inst`: `W^{-d}B_{1/16,0} ≤ 3W^{-3} → 0`), size and scale ranges, `STPsiClass` (`Ψ0_class`), `H = 0` Hermitian with `‖G−M‖_max = 0 ≤ δ₀` (`STGMM_zero`). Left as hypotheses (other gates' pins): `STLK`, `STDecay`, `STStep1Loop`, `STStep1Weak`, `STInitialGT2`, `STLWassm(Exp)`, the per-time premises of `STNetLift2`, and the nine pins of the skeleton. `inst_Bdata` (the size data) and `inst_stop` (the stopping time) take no pin: both are proved.
### b.5 Name clash, copies, ports
```
$ python3 fqn_clash.py RBM3D/Probe/T2039Pins.lean /Users/junyin/Lean_proof/RBM3D     # namespace-aware, main at 37a8655
probe declarations: 285 (285 public); library declarations at main (without Probe/): 2883 fully qualified names
fully qualified public probe names that also occur in the library: 0
public probe names outside RBM.Probe.*: 105; of them clashing: 0
$ python3 cmp_defs.py <37 names> | awk '{print $NF}' | sort | uniq -c    # copies vs merged Induction/Defs.lean (24), Step34Pins.lean (4 bundle + 9 hierarchy terms)
     37 IDENTICAL
$ grep -c 'RBM2D\|RBM1D' RBM3D/Probe/T2039Pins.lean
6
$ python3 cites.py docs/reports/T2039-portmap.md      # every RBM2D file:line citation of P.1-P.8 against c9a24cf (file exists, range inside the file)
citations 42; RBM2D files 18; RBM3D citations (not checked) 4; not found anywhere: []; line range beyond the file: []; failures 0
```
Ports from RBM1D/RBM2D: none (the 6 lines are docstring citations; no text copied, so no diff-stat). Copies of RBM3D files: T2015 probe `752e027` (§0, the `sz0` data of §13) and `Step34Pins.lean` at `56c30fb` (§12.1, §12.2), each tagged with its source lines.
### b.6 Extreme inputs (TEAM §8 lesson 25; the scripts are verbatim in portmap P.10; F14)
```
$ python3 contract.py 3         # STContractPt: eta down to 0.005, band and full H
d=3 W=2 L=3 N=216: min Re L6 = 2.283e-12 (>=0); max pointwise L6/(sqrt(L4alt)*|L4'|) = 0.9734; max LHS/RHS(const 3^d) = 0.4018
$ python3 ttt2.py | awk '$1==24 && $2==0.5 && /\(ii\)/'     # (TTT2), core of STNewKLK: R = max_a (1-u)(T_u*T_t)(a)/T_t(|a|), L = 24
 24     0.5 (ii) u=t, 1-t=g^2/L^2                   2.913      2.173
 24     0.5 (ii) u=t, 1-t=g^2/L^d (extreme)         0.700      0.679
 24     0.5 (ii) 1-u=g^2/L^2, 1-t=g^2/L^d           2.324      1.570
 24     0.5 (ii) 1-u=1-t=1e-3 g^2/L^d               0.609      0.619
$ python3 ttt2big.py            # regime (i), u = t, 1-t = 0.5, g = 0.1, L large: both norms saturate, the L^inf constant is about 3 times the l^1 one
L= 12  (i) u=t, 1-t=0.5: R_Linf=   106.8 R_l1=    74.5   |  (i) 1-u=1, 1-t=0.01: R_Linf=   107.7 R_l1=    74.8
L= 24  (i) u=t, 1-t=0.5: R_Linf=   293.3 R_l1=   167.0   |  (i) 1-u=1, 1-t=0.01: R_Linf=   296.1 R_l1=   168.5
L= 48  (i) u=t, 1-t=0.5: R_Linf=   645.7 R_l1=   283.2   |  (i) 1-u=1, 1-t=0.01: R_Linf=   652.1 R_l1=   285.9
L= 72  (i) u=t, 1-t=0.5: R_Linf=   915.9 R_l1=   330.4   |  (i) 1-u=1, 1-t=0.01: R_Linf=   924.9 R_l1=   333.7
L= 96  (i) u=t, 1-t=0.5: R_Linf=  1111.4 R_l1=   341.5   |  (i) 1-u=1, 1-t=0.01: R_Linf=  1122.4 R_l1=   344.8
$ python3 theta_decay.py        # STK2decay: max_a |Theta_{uM}(0,a)| / (B_{u,|a|_inf} exp(-sqrt(|a|_inf/ell_u))), L <= 48, M in {1, -1, e^{2 pi i/3}}, 1-u down to 1e-3 g^2/L^d
theta_decay.py: rows=120  max ratio=2.028
$ python3 scale_family.py       # STScaleExists: K_0 = 0, T_u(K_{m+1}) = b_u^{1/6} T_u(K_m) cut at L, along sz0, x = 1-u from 1 down to N^(-1+eps) (below g^2/L^d); 8 rows, all monotone; rows n = 0, 9 at D = 10
 n    L          W          g x_min=N^-.9    g^2/L^d   grid T_u(K_m) monotone in u    D maxM
 0    4         32     0.0156   2.04e-06   3.81e-06     24     True                         10   8
 9   40    3.2e+06   1.56e-08   1.29e-22   3.81e-21     81     True                         10   7
$ python3 mat_extreme.py 3 80; python3 mat_extreme.py 4 40    # STStep2Local/Avg: 1-u from 2g^2/L^d down to 0.1 g^2/L^d (rows 1-3 of each block shown)
d=3 W=2 L=3 N=216 g=0.50 samples=80;  g^2=0.25 g^2/L^2=0.02778 g^2/L^d=0.009259
1-u = 2 g^2/L^d          x=0.0185 N*eta=4.00  mean-ratio[0.52..0.61]  max-ratio 19.0  trace-ratio 0.71
1-u = g^2/L^d (extreme)  x=0.00926 N*eta=2.00  mean-ratio[0.68..0.75]  max-ratio 56.0  trace-ratio 0.80
1-u = 0.3 g^2/L^d        x=0.00278 N*eta=0.60  mean-ratio[0.86..1.14]  max-ratio 169.5  trace-ratio 0.85
d=3 W=2 L=4 N=512 g=0.50 samples=40;  g^2=0.25 g^2/L^2=0.01562 g^2/L^d=0.003906
1-u = 2 g^2/L^d          x=0.00781 N*eta=4.00  mean-ratio[0.54..0.64]  max-ratio 22.8  trace-ratio 0.80
1-u = g^2/L^d (extreme)  x=0.00391 N*eta=2.00  mean-ratio[0.71..0.78]  max-ratio 40.7  trace-ratio 0.88
1-u = 0.3 g^2/L^d        x=0.00117 N*eta=0.60  mean-ratio[0.95..1.25]  max-ratio 113.9  trace-ratio 0.96
```
### b.7 Items 1 and 7 (full tables in the portmap)
```
$ python3 inv2039.py table | tail -1       # item 1: the 46 RBM2D ST-2 files at c9a24cf; kept lines at 0c1330a
| | TOTAL 46 files | 41618 | 31831 | classes {'b': 30, 'c': 16} | 914 | 605 | |
$ python3 mksplit.py | tail -1; stderr     # item 7: split table P.5
| total | | | | 25377 | 41300 | | A 4840 + B 13550 + C 22910 |
TICKETS=41  groupA=4 groupB=16 groupC=21  lines=41300
```
**Narrative.**
1. Stage 1b was rerun on `t/T2039` from the WIP commits of the interrupted run. The probe has §0 (the 24 ST-1 pins, copies) to §14 (axioms): vocabulary and measurability (§1), the pins (§2), real-number core, tails, transfer, engine, good event, iteration (§3–§11), the pins `STScaleExists`, `STOptL2`, `STLocalAvgOfL2`, the size data (proved) and the skeleton `ST_step2_of_pins` (§12), the bridge to T2049 (§12.1), the general-`n` grid pin (§12.2), the instances (§13).
2. Items: 1 → P.1, P.2; 2 → probe §2, §12.2; 3 → (a) and P.3; 4 → P.4; 5 → `ST_step2_of_pins` (nine pins as hypotheses); 6 → P.6; 7 → P.5; 8 → §13, b.4.
3. The skeleton proves the size data, the good event of the grid walk from the pins, the stopped Grönwall bootstrap, the iteration over scales, `(Eq:Gdecay_w)` and `(eq:L2_decay)`. Constants: `C_d = 3C + 1` (`C` of `lem:newKLK`), `𝔠_d = min(1/100, 1/(60 C_d), 𝔠₀)`; `C_d𝔠_d ≤ 1/60` implies the preflight's derived constraint `𝔠_d(C_0+1/6) < 1/30` at `C_0 = C_d`.
4. Reconciled with what `main` merged after the branch base (F12–F16): the 37 copied declarations are identical to the merged ones (b.5); the bundle `STStep2Concl` of T2049 is implied (compiled; `STAvgU` through `𝓛^{(1)}_- = conj 𝓛^{(1)}_+`); one name clash, `STContract` (the merged pin is the Step 3 inequality, mine the pointwise Step 2 one), removed by the name `STContractPt`; the drift algebra `HierAlgebra`, `HierarchyN` that T2041 F-D leaves to ST-2 is row ST2-28a, `StoppedEndDefs` is proposed dropped (T2049 pins `STOeqNQ`, `STOeqQt`, `STOeqQtNZ`); the LW pins agree with those of T2040 up to five differences of form (F15).
5. `STGridRepN` pins `Sol_CalL` and both inequalities of `lem:DIfREP` for every loop length (decomposition, remainder, plain and `𝒰`-weighted Azuma tails of the same martingale); `ST_gridMart_of_repN` shows by list computation that the loop-length-2 pin of the skeleton is its case `m = 2`.
6. Split: 41 tickets, 41 300 lines (A 4 / 4 840, B 16 / 13 550, C 21 / 22 910): above the O2 band of 40, not above 50, so Jun is not asked; without the four `lem_dec_calE` rows (ST2-36..39, used by the paper in Step 5, 3_5:2317) it is 37. Risk (P.4): high ST2-09..11 (`lem: EMn2_N`); medium–high ST2-12/13 (`STGridRepN`); medium `STNewKLK`, `STContractPt`, `STOptL2`, `STLocalAvgOfL2`; ST2-32 (`GridGoodN` without its class-c imports) needs a rewrite.
7. Not verified by Lean: the truth of the owed pins (hence b.6) and the `d = 3` constants; the numeric checks carry no explicit `≺` constant.

## (c) Verified Mathlib names
All 143 distinct names of the probe in the namespaces Real, Finset, Filter, MeasureTheory, Matrix, Complex, Nat, Fin, List, Set, ... resolve by `#check` (`mathlib_names.py` writes the `#check` file, P.10; 0 errors). Selected, with the checked statements:
Real.rpow_le_rpow_of_exponent_ge: 0 < x → x ≤ 1 → z ≤ y → x ^ y ≤ x ^ z
Real.rpow_le_rpow_of_nonpos: 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.rpow_le_one_of_one_le_of_nonpos: 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
Real.one_sub_inv_le_log_of_pos: 0 < x → 1 - x⁻¹ ≤ Real.log x
Real.log_div: x ≠ 0 → y ≠ 0 → Real.log (x / y) = Real.log x - Real.log y
Finset.measurable_sup': (∀ n ∈ s, Measurable (f n)) → Measurable (s.sup' hs f)
Finset.sum_pair: a ≠ b → ∑ x ∈ {a, b}, f x = f a + f b
Fin.forall_fin_two: (∀ i : Fin 2, p i) ↔ p 0 ∧ p 1
Complex.norm_conj: ‖(starRingEnd ℂ) z‖ = ‖z‖
Matrix.nonsing_inv_eq_ringInverse: A⁻¹ = Ring.inverse A
Matrix.conjTranspose_nonsing_inv: A⁻¹ᴴ = Aᴴ⁻¹
Matrix.trace_conjTranspose: Aᴴ.trace = star A.trace
Matrix.trace_mul_comm: (A * B).trace = (B * A).trace
Matrix.diagonal_conjTranspose: (diagonal v)ᴴ = diagonal (star v)
Names verified absent: none recorded in this run.

## (d) Open issues and paper-delta candidates
Open issues:
1. The light-weight inputs are owed (`STLWB`, `STLWT`, premises `STInitialGT2`, `STLWassm`, `STLWassmExp`): reconcile with T2040's `LWterm`, `LWtermExp` (F15: same bounds and exponents, five differences of form).
2. `(TTT2)` for `|·|_∞` is not available (the merged `EKPropT`, `Evolution/Pins.lean:139`, is `ℓ¹`; EK design T2016): row ST2-06b before ST2-07 (F1, b.6). `STK2decay` needs no bridge (pointwise, `|a|_1 ≥ |a|_∞`).
3. `lem:newKLK` is pinned deterministic (F5, from 3_5:615–668: Ward identity and `‖G−M‖_max ≤ δ₀` only). If ST2-07 finds the proof needs more, it stops and reports.
4. Dispatcher decisions: keep ST2-36..39 (`lem_dec_calE`) in ST-2 or move them to ST-4; drop `StoppedEndDefs` (F16); the count 41 against the O2 band of 40.
5. Not pinned here (ports or owned by ST-3): the algebraic Duhamel telescope (deterministic, ST2-27); the grid good events and stopping-time exits of Steps 3–4 (S3-10, S3-13a own them; the Step 3–4 pins of T2049 take `STStep2Concl`, `STLmaxU`, `STLKU` as hypotheses, not a good set).
6. When T2028 and T2049 are in the base, the copies of the probe are replaced by the merged names; ST2-01 defines `STStep2` with the conclusion `STStep2Concl` (`ST_step2_concl`).
7. Registry classes (DECISIONS §16, §20; P.7): owed: `STNewKLK` (ST2-07), `STContractPt` (ST2-08), `STEMn2Poly` (ST2-09), `STEMn2Exp` (ST2-10, 11), `STGridRepN` (ST2-12, 13, 27, 34, 35; `STGridMart` follows), `STK2decay` (ST2-06), `STNetLift2` (ST2-18, 19), `STScaleExists` (ST2-05), `STOptL2` (ST2-14, 15), `STLocalAvgOfL2` (ST2-16, 17), `STStep2`, `STStep2Concl` (ST2-04), `STLWB`, `STLWT` (LW gate), `STInitialGT2`, `STLWassm`, `STLWassmExp` (Step 1 / ST-6 chain); structural: `STPsiClass`; borrowed inside ST2-06, ST2-07: `Prop5Decay`.

Paper-delta candidates (the dispatcher numbers them): T2039a `lem:newKLK` pinned deterministic for every Hermitian `H` with `‖G−M‖_max ≤ δ₀` (paper: with high probability under `(Gtmwc)`; `C` from `prop:ThfadC`). T2039b `C_d`, `𝔠_d` have no numerals in the paper; pin `∃ C_d, ∃ 𝔠_d ≤ 10^{-2}` (`C_d` first), compiled closure `C_d𝔠_d ≤ 1/60`, `𝔠_d ≤ 𝔠₀` of `(eq:opt_L2)`. T2039c both light-weight families are inputs; `STLWB` ties the `(initialGT2)` control to `Ψ_t(0)`. T2039d "any large `D`" is `∀ D > 0` (`STStep2Decay`, `STLWT`, `STEMn2Exp`). T2039e the scale family of `(eq:def_ell1)` is cut at `L` (`STScaleAdm`). T2039f `(TTT2)` in `|·|_∞` needs its own proof (`EKPropT` is `ℓ¹`). T2039g `STStep2Avg` is the single-charge `tr((G_u−M)E_a)`; the merged `STAvgU` is two-charge, equivalent (compiled). T2039h `STGridRepN`: the BDG moment bounds become Azuma–Hoeffding tails on the grid (DECISIONS §7) with loss `N^{ε'}`, additive `N^{-D}` and remainder `N^{C₀}Δ^{1/2}`, for all `k ≤ K` at once. T2039i `STContractPt` has the explicit constant `3^d` and label-dependent maxima (the merged `STContract` is the Step 3 form).

## Repair (audit 1) — repairer claude-opus-5-5, written Sat Oct  3 14:10:18 UTC 2026
Defects of `T2039-audit.md` "Required for resubmission" 1–4; commit `0362cbc` on `t/T2039` (probe only; portmap P.9 block of `STScaleOk`/`STScaleAdm` regenerated from probe lines 2277–2281, 2288–2296). Fix: `STScaleOk` (u-monotonicity) and `STScaleAdm` (third clause `0 ≤ K_m ≤ K_{m+1}`, fourth clause the scale step) are now required `∀ m, ∀ᶠ n in atTop`; `K_0 = 0` stays for every `n` (it forces nothing). `ST_next`, `ST_iterate`, `ST_decay_pt`, `ST_selfImprove_section` take the eventual clauses (same line numbers). New §15 (probe :5903–6041): `ST_scaleAdm_congr` (finitely many `n` of `sz`, `s`, `t`, `K_{m≥1}` impose nothing) and `inst_scaleAdm_szX` at the audit-1 data; `szX`, `zX`, `flow_zX`, `szX_Bctl_00` are copied from the auditor's `scratchpad/T2039/ScaleCex.lean`.
```
$ sed -n '2277,2281p;2288,2296p' RBM3D/Probe/T2039Pins.lean      # new statements (STScaleOk, STScaleAdm)
def STScaleOk (s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ) : Prop :=
  (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧ Kf n u ≤ ((sz.L n : ℕ) : ℝ) ∧
    Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u) ∧
  (∀ᶠ n in atTop, ∀ u v, s n ≤ u → u ≤ v → v ≤ t n →
    tailT d (sz.L n) (sz.lam n) u (Kf n u) ≤ tailT d (sz.L n) (sz.lam n) v (Kf n v))
def STScaleAdm (s t : ℕ → ℝ) (Kseq : ℕ → ℕ → ℝ → ℝ) : Prop :=
  (∀ n u, Kseq 0 n u = 0) ∧ (∀ m, STScaleOk sz s t (Kseq m)) ∧
  (∀ m, ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kseq m n u ∧ Kseq m n u ≤ Kseq (m + 1) n u) ∧
  (∀ m, ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * tailT d (sz.L n) (sz.lam n) u (Kseq m n u) ≤
      tailT d (sz.L n) (sz.lam n) u (Kseq (m + 1) n u)) ∧
  (∀ D : ℝ, 0 < D → ∃ M : ℕ, ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
    tailT d (sz.L n) (sz.lam n) u (Kseq M n u) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) ∨
      ((sz.L n : ℕ) : ℝ) ≤ Kseq M n u)
$ sed -n '5917,5922p;6016,6021p' RBM3D/Probe/T2039Pins.lean      # the check (audit item 3)
theorem ST_scaleAdm_congr {d : ℕ} (sz : Sizes d) {sz' : Sizes d} {s t s' t' : ℕ → ℝ} {K K' : ℕ → ℕ → ℝ → ℝ}
    (hL : ∀ᶠ n in atTop, sz'.L n = sz.L n) (hlam : ∀ᶠ n in atTop, sz'.lam n = sz.lam n)
    (hW : ∀ᶠ n in atTop, sz'.W n = sz.W n)
    (hs : ∀ᶠ n in atTop, s' n = s n) (ht : ∀ᶠ n in atTop, t' n = t n)
    (hK : ∀ m, ∀ᶠ n in atTop, ∀ u, K' m n u = K m n u) (hK0 : ∀ n u, K' 0 n u = 0)
    (h : STScaleAdm sz s t K) : STScaleAdm sz' s' t' K' := by
theorem inst_scaleAdm_szX (K : ℕ → ℕ → ℝ → ℝ)
    (hK : STScaleAdm sz0 (fun _ => 0) (fun n => lemT (zX n)) K) :
    STFlow szX (1 / 10) (1 / 10) (1 / 6) (1 / 10) zX ∧ 1 < szX.Bctl 0 0 ∧
      STScaleAdm szX (fun _ => 0) (fun n => lemT (zX n)) K ∧
      STScaleAdm szX (fun _ => 0) (fun n => lemT (zX n))
        (fun m n u => if n = 0 then 0 else K m n u) := by
$ lake build RBM3D.Probe.T2039Pins   # Sat Oct  3 14:08:27 -> 14:09:08 UTC 2026 -> "Build completed successfully (3739 jobs)." exit 0
$ grep 'depends on axioms' build.out | sed 's/.*: //' | sort | uniq -c   ->   33 [propext, Classical.choice, Quot.sound]   (31 before + 2 new)
$ grep -E 'inst_skeleton|ST_step2_of_pins|ST_scaleAdm_congr|inst_scaleAdm_szX' build.out   (each: [propext, Classical.choice, Quot.sound])
5875 inst_skeleton  5876 inst_skeleton_concl  5891 ST_step2_of_pins  5898 inst_skeletonN  5900 ST_step2_of_pinsN  6040 ST_scaleAdm_congr  6041 inst_scaleAdm_szX
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom' RBM3D/Probe/T2039Pins.lean | wc -l     -> 0
$ lake env lean ScaleCexRerun.lean   # auditor's refutation, unchanged  ->  exit 1; ScaleCexRerun.lean:65:17: error: Function expected at
$ grep -rnw <name> RBM3D ../RBM3D/RBM3D --include='*.lean' | grep -v Probe/T2039Pins.lean | wc -l  ->  ST_scaleAdm_congr szX szX_W szX_lam szX_size szX_admissible szX_one_le_size zX zX_locDomain zX_im_pos flow_zX szX_Bctl_00 inst_scaleAdm_szX: 0 each
```
`ST_step2_of_pins`, `ST_step2_of_pinsN` and `inst_skeleton*` recompile against the restated pin unchanged in their statements. `STScaleExists` itself stays an owed pin (ST2-05); the check shows the auditor's data no longer refutes it, not that it holds. Paper-delta candidate T2039j: the clauses of `STScaleAdm`/`STScaleOk` (`(eq:def_ell1)`, `(eq:monotone_Ku)`) are required only for large `N` (eventually in `n`, per level `m`); the paper states them at fixed `N`, in the regime `W^{-d}B_{u,0} ≤ N^{-c}`.
