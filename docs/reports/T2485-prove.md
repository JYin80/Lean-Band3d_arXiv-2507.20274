Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 03:25:48 UTC 2026

Setting (targets 3, 4: `d = 3`; targets 1, 2: every `d`): `N = (WL)^3`, `τ_u = (W^d(1-u))⁻¹`, `τ₀ = τ'/2`, `ρ = (1-s)/(1-u)`, `$S = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2485`.
`G_n` := complement of the union of 7 `PrecL` bad sets at `(τ₀, D₁+1)` (the union over `u` is inside each set, so `G_n` does not depend on `u`).

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| `τ₀` | `τ'/2` | `2^{k-1}N^{τ₀} ≤ N^{τ'}` (k ≤ 6), `4N^{τ₀} ≤ N^{τ'}` ((vi)), `2N^{τ₀} ≤ N^{τ'}` ((ii),(iv)) ⇔ `N^{τ'/2} ≥ 32` | `N ≥ 32^{2/τ'}` = 1.0e3 / 1.0e6 / 1.3e30 at τ' = 1 / 1/2 / 1/10; instance (n=100): `N^{τ'/2}` = 4.0e10 |
| probability | 7 events: (iv); (v) k=2,3,4,6; (vi) `STLKUgL` k=2 and `STGdecayWgL` | `7N^{-(D₁+1)} ≤ N^{-D₁}` ⇔ `N ≥ 7`; violator step needs `P(univ)=1 > N^{-1}` | `N ≥ 7` vs 2.5e42 |
| `Bctl ≤ 2τ_u` | `Bctl = W^{-d}[(g²+1-u)⁻¹ + (L^d(1-u))⁻¹] ≤ (1+L^{-d})τ_u ≤ (28/27)τ_u` | `1-u > 0` | 2 vs 1.037 |
| `STWB(K) ≤ Bctl` | `((K+1)^{d-2})⁻¹ ≤ 1` | none | exact at `K=0` |
| `ellT = 1` | `min(max(g/√(1-u),1),L)` | `g² ≤ 1-u` (STReg5III, `u ≤ t`), `L ≥ 1` | `lam² = 2.2e-28 ≤ 1/2` (n=100) |
| `ρ ≤ W^d`, `τ⁻¹ ≤ W^d` | `ρ ≤ (1-u)⁻¹ ≤ lam⁻² ≤ W^d`, `1-u ≤ 1` | `1 ≤ lam²W^d` (from `W^{2𝔡} ≤ lam²W^d`, `Defs/Sizes:193`) | `W^{2𝔡}` = `W^{0.2}` |
| (vi) constant | `4^{1-θ}2^{6θ/5} = 2^{2-4θ/5} ≤ 4` | `θ > 0` | 3.9978 at θ = 0.001 |
| (vi) power of `W` | `ρ^{Cdθ}τ^{-4θ/5} ≤ W^{θd(Cd+1)}`: exponents `dCdθ + 4dθ/5 ≤ θd(Cd+1)` | `Cd ≥ 0` (`Cd ≥ -1/5` with `ρ ≥ 1`) | `θd/5 = 0.06` (θ=1/10); grid max ratio 0.909 |
| `θ` | `0 < θ < 1` | `A₁^{1-θ}` needs `θ ≤ 1`; the min-inequality is false for `θ > 1` | strict |
| floor `D''` | `D'' = D + τ'/𝔠 + 1` | `N^{τ₀}W^{-D''} ≤ W^{-D}`, `N^{τ₀} ≤ W^{τ₀/𝔠}` (`Defs/Sizes:237`) | `τ'/(2𝔠)+1` = 2.5 in the exponent |
| (iii) amplitude | `W^{-d}W^{-(D+d)} ≤ W^{-D}` | `W ≥ 1` | `W^{-2d}` |
| (iii) window | `ℓ* = (log W)^{3/2} ≤ L/2` | nonempty iff | `sz0`: n ≥ 57; **n = 1 collapsed** (18.25 > 4) |
| target 4 | `4 ≤ log W`; `(L^dW^{6d})² ≤ W^D` | `W ≥ N^𝔠 → ∞`; `L^d ≤ N ≤ W^{1/𝔠}` gives `W^{2/𝔠+12d} = W^{D0}` | `D*-2d ≥ D0+1` (design `PfStep5:34` params) |
| walk level | `D_u = D* + 2 log(1-u)/log W` | `W^{2𝔡-d} ≤ lam² ≤ 1-u ≤ 1`, `log W > 0` | `D*-2d+4𝔡 ≤ D_u ≤ D*`; 4𝔡 = 0.4 |
Constants depend on `d` and fixed exponents only; no `lam0 ≤ lam`, no `A`, no entry-level bound, no `|E|<2`, no `M = mI`, no `‖m‖ = 1` is used.

Numerics (iii):
```
$ python3 -I $S/vi_chain.py   # d=3, W in {e^4,1e3,1e6,1e12}, L in {3,8,100,1000}, lam²W³ in {1,4,100}, 1-t in {lam²,.01,.5}, s in {0,.1,.5}, u in {s,(s+t)/2,t}, K in {0,1,10,1000}, θ in {.5,.1,.02}, Cd in {.5,1,4}
points: 41472
max ratio = 0.908593 (required <= 4) at (W,L,c,1-t kind,s,1-u,K,theta,Cd)=(54.598, 3, 1.0, 'lam2', 0.0, 1.0, 0, 0.02, 0.5)
$ python3 -I $S/thresholds.py | sed -n '1p;3,5p;7,9p'
tau'   N>=4^(2/tau')   N>=32^(2/tau')   binding N_min = max(7, 32^(2/tau'))
1      16              1024             1024
0.5    256             1.049e+06        1.049e+06
0.1    1.1e+12         1.268e+30        1.268e+30
(b) max over 1e5 samples of log(N^tau0 W^-D'') - log(W^-D)  (<= 0 required): 0.000e+00
(c) max_th 4^(1-th) 2^(6 th/5) over th in (0,1) = 3.997783 (<= 4); 1+1/L^3 at L=3: 1.037037 (<= 2)
(d) violations of  D*-2d <= D_u <= D*  over 1e5 samples: 0
$ python3 -I $S/interp.py   # a <= min(A1, A2 e^{-√r}+F) against A1^(1-θ)A2^θ e^{-θ√r}+F, 5e5 random (A1,A2,F,θ,r)
samples 500000 violations of  a <= A1^(1-th) A2^th exp(-th sqrt r) + F : 0 ; max (a-rhs)/rhs = 0.0
```

Route per conjunct of `T2485_BAMatrix` (all on `G_n ∩ {n large}`; `H = seqHflowBA`, `LM n u H = BALloop` by `rfl`, `baStep2Mat_LM` `Step2BA:79`):
| conjunct | source | step |
|---|---|---|
| Hermitian | `BAAuxGraph2_seqHflowBA_herm` `BAAuxGraph2:448` | direct |
| (i) | target 1 | `J♯` is the `sup'` |
| (ii) | `baKbound_holds` `KBound:245` = `STKboundgL` k=2 (deterministic `K`) | violator sequence `u_n`; `P(univ)=1>N^{-1}`; `‖K‖ ≤ N^{τ₀}Bctl ≤ 2N^{τ₀}τ_u ≤ N^{τ'}τ_u` |
| (iii) | `baEMn2ExpHK` `EMn2BA:637` at `t := u_n`, `D` | `ellT=1` so `emn2ExpEllStar = (log W)^{3/2}`; `W^{-d}W^{-(D+d)} ≤ W^{-D}` |
| (iv) | `STAvgUgL` `Step2Gen:491`; `baKsol_one` `KInduct:77` (`0<lam0` from `BAflow_lam0_window` `GreenSchur:72`, `BAflow_real` `:59`) | `K^{(1)} = PropSpin m = STmsigg` (`Step2Gen:346`); `Bctl ≤ 2τ_u` |
| (v) k=2,3,4,6 | `STLmaxUgL` `Step34Gen:58` | `N^{τ₀}Bctl^{k-1} ≤ 2^{k-1}N^{τ₀}τ_u^{k-1} ≤ N^{τ'}τ_u^{k-1}` |
| (vi) | `STLKUgL` `Step34Gen:65` (k=2), `STGdecayWgL` `Step2Gen:503` at `D''` | `x := ‖(L-K)^{(2)}‖/N^{τ₀} ≤ A₁ = Bctl² ≤ 4τ²`, `x ≤ A₂e^{-√r}+W^{-D''}`, `A₂ = ρ^{Cd}Bctl^{1/5}STWB ≤ ρ^{Cd}(2τ)^{6/5}`; `min ≤ A₁^{1-θ}A₂^θ`; `A₁^{1-θ}A₂^θ ≤ 4W^{θd(Cd+1)}τ²`; floor `N^{τ₀}W^{-D''} ≤ W^{-D}` |
Probability: `P(G_nᶜ) ≤ 7N^{-(D₁+1)} ≤ N^{-D₁}` (`measure_union_le`; `isProbabilityMeasure_seqP` `FineModel:171`); band template `lemDecCalEPrec_fixed/_union7` `LemDecCalEPrec:692/705` (private; copy under the stem).

Proof of target 2 (`D' ≤ D`; `X(σ,a) := ‖STLKMg(σ,a)‖` does not depend on `D`, `J`): Hermitian, (ii), (iv), (v) carry neither `D` nor `J`, so they are unchanged. (i) at `(D', J♯(D'))` is target 1 at `D'`. (iii): `W ≥ 1` (`W_pos`) and `-D ≤ -D'` give `W^{-D} ≤ W^{-D'}`. (vi): `X ≤ P + W^{-D} ≤ P + W^{-D'}`, `P` the `D`-free main term. The hypothesis at `(D, J)` is used only in (iii), (vi). No size, `d` or `u` hypothesis.
Proof of target 4 (`BAFlow ⇒ Admissible`: `0<𝔠`, `0<𝔡`, `SizeTendsto`, `Bandwidth 𝔠`, `WO 𝔡`). Eventually: `WO` gives `W^{-d/2+𝔡} ≤ lam` so `lam > 0`; `log W ≥ 4` because `W ≥ N^𝔠 → ∞`; the premise gives `(L^dW^{6d})² ≤ W^D`. For `u ∈ [s_n,t_n]`, `D' ≥ D`, `1 ≤ J ≤ W^{1/2}`: `3 ≤ 3`; `0 ≤ s_n ≤ u`; `lam² ≤ 1-t_n ≤ 1-u` (STReg5III) and `lam > 0` give `u ≤ t_n < 1`; `1 ≤ W^{2𝔡} ≤ lam²W^d` (`lam_sq_mul_pow_ge`; `W ≥ 1`, `𝔡>0`); `1 ≤ N^{τ'}` (`N ≥ 1`, `τ' ≥ 0`) for `Λ` and `K₀`; `4 ≤ log W`; `(L^dW^{6d})² ≤ W^D ≤ W^{D'}` (`W ≥ 1`); `1 ≤ J ≤ W^{1/2}`. All twelve conjuncts of `T2485_BAScalar`. U5d takes `D := D*-2d`, `D' := D_u`.

Line estimate (central/lo/hi; rows in `$S/sizes.py`; 1b copies of `LemDecCalELip_Jsharp_basic:941`, `lemDecCalEPrec_fixed/_union7` are in the rows):
```
$ python3 -I $S/sizes.py
F1 lo/central/hi = 795 / 1090 / 1745        (Step5IIIGood: targets 1-3; regime 125, constant chain 100, violator + (ii) + (iii) 185, probability 90, conclusion on G 150, main 115)
F2 lo/central/hi = 240 / 340 / 560          (Step5IIIGood2: target 4 100; instances 5(a)-(c) 190)
total lo/central/hi = 1035 / 1430 / 2305   (ticket 700/1100/1650); split rule: central > 1950? False; any file central/hi > 1800? False
2.6 x central: F1 2834, F2 884, total 3718 (TLC-4 upper reference; ticket's 2.6 x 1100 = 2860)
```
The pre-signed split does not apply (central 1,430 ≤ 1,950; no file's hi above 1,800: no reserve). F1 at the 2.6× reference (2,834) would pass 2,000: the 1b watches 1,800 per file.

### (ii) One nondegenerate instance
`sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`), flow `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `s=1/10 < t=1/2 ≤ T0` (`T0 ≥ 2/3`), `D=40`, `Cd=1`, `θ=1/10`, `τ'=1/2`, `D₁=1`, `u ∈ {1/10, 3/10, 1/2}`:
```
$ python3 -I $S/instance2.py
n=1: L=8 W=1024 lam=2.441e-04 N=5.498e+11
  STReg5III lam^2=5.96e-08<=1/2 True | Bandwidth N^c=90.51<=W True | WO True | lam^2W^3=64>=1 True
  log W=6.931>=4 True | N>=7 True | N^(tau'/2)=861.1>=32 True | log_W(L^3W^18)^2=37.800<=40 True | floor(D''=44) True
  (iii) window l*=(log W)^(3/2)=18.25 vs L/2=4.0: EMPTY (collapsed, degenerate)
  (vi) ratio at u=s,.3,t: ['8.2e-02', '8.2e-02', '8.3e-02'] (<=4) | level D_u: ['39.9696', '39.8971', '39.8000'] in [D-2d,D]=[34,40]
n=100: L=404 W=336323216032 lam=1.472e-14 N=2.509e+42
  STReg5III lam^2=2.17e-28<=1/2 True | Bandwidth N^c=1.166e+07<=W True | WO True | lam^2W^3=8.242e+06>=1 True
  log W=26.541>=4 True | N>=7 True | N^(tau'/2)=3.98e+10>=32 True | log_W(L^3W^18)^2=37.357<=40 True | floor(D''=44) True
  (iii) window l*=(log W)^(3/2)=136.74 vs L/2=202.0: nonempty
  (vi) ratio at u=s,.3,t: ['7.0e-05', '7.1e-05', '7.1e-05'] (<=4) | level D_u: ['39.9921', '39.9731', '39.9478'] in [D-2d,D]=[34,40]
first n of sz0 with (log W)^(3/2) <= L/2 (nonempty (iii) window): 57
```
Every hypothesis of targets 1-4 holds at `n=100`; `BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` is the merged `flow_sz0` (`FlowPins`), `T0 ≥ 2/3` is `t0_sz0`. At `n=1` the window of (iii) is collapsed: the ticket's 5(c) (targets 1, 2 only, no windowed conjunct) is unaffected; 5(a), 5(b) are `∀ᶠ` statements about the sequence `sz0`, nonempty from `n = 57`. The bundle text check (stop rule 2), copies against the T2482 1a-audit probe text:
```
$ git --no-optional-locks show t/T2482:RBM3D/Probe/T2482Pins.lean | python3 -I $S/bundle_diff.py /dev/stdin
BAScalar T2485-check == T2482-probe(t/T2482 0ac2aab8+): True  T2485-check == T2482-check: True  chars 363
BAMatrix T2485-check == T2482-probe(t/T2482 0ac2aab8+): True  T2485-check == T2482-check: True  chars 1580
```
External premises (`STAvgUgL`, `STLmaxUgL`, `STLKUgL`, `STGdecayWgL`): limit computation at `u = 0`, `k = 1, 2` in the bulk (`H_0 = g₀Ψ` since `seqHflow = √u X`; `z_0 = E+m` (`ztOf`); `G_0 = M^B ⊗ I`, `m = L^{-d}tr M^B` (`BASelf`); `L^{(1)}_{0,+,a} = M_aa`, `L^{(2)}_{0,(+,-),(a,b)} = W^{-d}|M_ab|²`, `W^dBctl(0) = (g₀²+1)⁻¹+L^{-d}`):
```
$ python3 $S/ext_limit.py | sed -n '1,9p'      # (numpy; E = 0, 1; L^3 torus, nearest-neighbour Ψ^B)
L  g0     E   Im m   |M_aa-m|   |m|^2/B(0)  max_b|M_ab|^2/B(0)   rate c=-log|M_x|^2/(2|x|_inf) at |x|_inf=L/2
8   0.0156 0   0.9993  1.05e-13   0.9968      0.9968           3.989
8   0.0156 1   0.8656  5.38e-14   0.9968      0.9968           3.988
8   0.3000 0   0.8238  4.45e-16   0.7381      0.7381           1.386
8   0.3000 1   0.7402  8.08e-16   0.7262      0.7262           1.399
16  0.0156 0   0.9993  7.41e-14   0.9985      0.9985           4.077
16  0.0156 1   0.8656  5.05e-14   0.9985      0.9985           4.075
16  0.3000 0   0.8237  6.66e-16   0.7394      0.7394           1.329
16  0.3000 1   0.7402  9.16e-16   0.7276      0.7276           1.307
```
So `L^{(1)}_0 = m` (the solver residual is 1e-13: STAvgUgL's `K^{(1)} = m` is the right normalisation, no extra factor), `W^d L^{(2)}_{0,(+,-),(a,b)} = |M_ab|² ≤ 0.9985·W^dBctl(0)` (STLmaxUgL k=2 is consistent with `Λ = N^{τ'} ≥ 1`, no factor `W^d` mismatch), and `|M_x|² ≈ e^{-2c|x|_∞}` with `c ≈ 4.0` against `ln 64 = 4.16` at `g₀ = 1/64`. The `L=32` rows reach the double-precision floor and are not used. `K^{(2)}_0` is not computed here.

Verdict: target 1 PASS; target 2 PASS; target 3 PASS (needs `0<ε`, `0<𝔡`, `0<Cd`, `0<θ<1` as pinned; no further hypothesis, entry-level bound, `|E|<2` or `‖m‖=1`); target 4 PASS; split not triggered (central 1,430). Name-level items (iv file:line beyond the table, (ix) name-clash greps) are deferred to the head of the 1b report (ticket note (9)).

## (b) Script output (stage 1b, t/T2485 @ 10152ee4, Tue Oct 13 04:03:44 UTC 2026)
```
$ python3 -I iv.py   # note (9) (iv): merged sources used, name file:line (located by name on this branch); (vi) is in (a)
  BAAuxGraph2_seqHflowBA_herm Graph/BAAuxGraph2:448  |  baKbound_holds BA/KBound:245  |  baEMn2ExpHK BA/EMn2BA:637  |  baKsol_one BA/KInduct:77
  BAflow_real BA/GreenSchur:59  |  BAflow_lam0_window BA/GreenSchur:72  |  EMn2BA_T0_lt_one BA/EMn2BA:106  |  STAvgUgL Chain/Step2Gen:491
  STGdecayWgL Chain/Step2Gen:503  |  STLmaxUgL Chain/Step34Gen:58  |  STLKUgL Chain/Step34Gen:65  |  lam_sq_mul_pow_ge Defs/Sizes:193
  size_rpow_le_W_rpow Defs/Sizes:237  |  emn2ExpEllStar Induction/EMn2Exp1:176  |  STtailTD Induction/Step5Pins:151  |  STWB Induction/Defs:69
  STReg5III Induction/Step5Pins:58  |  StochDomAt Defs/StochDomAt:61  |  badSetAt Defs/StochDomAt:53  |  isProbabilityMeasure_seqP Gauss/FineModel:171
  flow_sz0 BA/FlowPins:1214  |  half_lt_t0 BA/FlowPins:1254  |  sz0_lam_pos BA/FlowPins:1184  |  lemDecCalEPrec_union7 (copy) Induction/LemDecCalEPrec:705
$ clash.sh   # (ix) final names (patterns in the script) on main, every t/* branch, the checks dir; the proposal names gave 0 hits at 03:28:04 UTC, before any Lean
main@94e626a1: files with hits = 0
branches scanned (t/*, excluding t/T2485): 494; branches with hits: 0
checks dir files (excluding T2485-check) with hits: 0
$ lake build RBM3D.BA.Step5IIIGood RBM3D.BA.Step5IIIGood2 2>&1 | tail -1;  warnings in the two files (grep -c): 
Build completed successfully (3900 jobs).
warnings in the two files: 0
$ wc -l (stop line 2,000 per file; split only if central > 1,950: not triggered)
     704 RBM3D/BA/Step5IIIGood.lean,      198 RBM3D/BA/Step5IIIGood2.lean; at the section commits (git show | wc -l): 40e6e696 595 | 52d4df3e 694 + 193 | 10152ee4 704 + 198
$ lake env lean ax_all.lean   # #print axioms of the 9 public declarations below
BAStep5IIIJsharp, baStep5IIIJsharp_spec, baStep5III_matrix_level, BAStep5IIIGood, BAStep5IIIGoodThm, baStep5IIIGoodThm_holds, baStep5III_scalar_flow, Step5IIIGood_reg_sz0, Step5IIIGood2_sz0_floor
  -> [propext, Classical.choice, Quot.sound]  (9 of 9)
$ extract.py   # statement ranges, file:lines name
  G1:314-317 BAStep5IIIJsharp  |  G1:327-331 baStep5IIIJsharp_spec  |  G1:349-374 baStep5III_matrix_level  |  G1:393-408 BAStep5IIIGood  |  G1:414-419 BAStep5IIIGoodThm  |  G1:434-434 baStep5IIIGoodThm_holds  |  G2:52-60 baStep5III_scalar_flow
$ sed -n "414,419p" Step5IIIGood.lean   # the pin of target 3
def BAStep5IIIGoodThm : Prop :=
  ∀ (κ ε 𝔠 𝔡 Cd : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < Cd → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
      STAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
      STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
        ∀ D : ℝ, 0 < D → BAStep5IIIGood sz z s t D Cd
$ lake env lean pins.lean   # = T2485-check Part 2 + 6 examples; rc; negative control
∀ d, T2485_JsharpSpec d;∀ d, T2485_MatrixLevel d;T2485_BAGoodThm;T2485_ScalarFlow;T2485_BAGood sz z s t D Cd ↔ BAStep5IIIGood sz z s t D Cd;T2485_BAGoodThm = BAStep5IIIGoodThm;
rc=0
negative control (example : T2485_BAGoodThm := baStep5III_scalar_flow) -> line 134:29: error: Type mismatch
$ python3 -I stmt_diff.py   # against probe t/T2459:Probe/T2459Pins.lean (:170 :186 :191) and the check body
(A) BAStep5IIIJsharp vs probe T2459_BAJsharp (:170): identical up to the name and whitespace
(B) BAStep5IIIGoodThm vs probe T2459_BAgoodThm (:191), hypothesis chunks, probe -> mine:
    +0 < ε
    +0 < 𝔡
    +0 < Cd
    -STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))
(C) BAStep5IIIGood vs probe T2459_BAgood (:186) outside the matrix part: identical after removing the two lets (H, J#): True
(a) STLmaxUgL (merged, Step34Gen.lean ) body == probe-local T2459_LmaxU body: True
(a) STLKUgL (merged, Step34Gen.lean ) body == probe-local T2459_LKU body: True
(D) target 2 hypothesis == T2485_BAMatrix body: True
(D) target 2 conclusion == body[D->D', J->J#(D')]: True
$ instances (first docstring line above each `example`; all compile in the build above)
Step5IIIGood.lean:631  Target 3 at the instance: `baStep5IIIGoodThm_holds` at `sz0` with the flow, the window, the 
Step5IIIGood.lean:641  Target 1 at the instance (`n = 1`: `L = 8`, `W = 1024`; `u = 1/2`, `H = 0`, level `30`): con
Step5IIIGood.lean:671  Target 2 at the instance, composed with target 3 (`D = 40 → D' = 30`, `θ = 1/10`, `Cd = 1`, 
Step5IIIGood2.lean:154  Target 4 at the instance (`τ' ≥ 0`, level `40`): the scalar part holds eventually, at every 
Step5IIIGood2.lean:165  The composed instance (audit O2; T2482 dispatcher answer (4)): at the instance (`D = 40`, `θ
$ greps on the two files (each: output, then rc)
C1 table words: 0 hits; statement words (STGridRepNgL, |E|, mSigma, SB d, E2Hyp, gexRHS, STGMMg, ≤ A *): 0 hits
withLam outside 'seqP (sz.withLam 0)' / 'seqP (SizesInst.sz0.withLam 0)': 0 hits; X1-C4 (def|abbrev|structure) of BAStep5IIIE*/STLmaxUgL/STLKUgL: RBM3D/BA/Step5IIIGood.lean:0 RBM3D/BA/Step5IIIGood2.lean:0 hits
sorry/admit/native_decide/axiom: RBM3D/BA/Step5IIIGood.lean:0 RBM3D/BA/Step5IIIGood2.lean:0 ; R1 text / Step 1 names (lam0_le_lam, baStep1): RBM3D/BA/Step5IIIGood.lean:0 RBM3D/BA/Step5IIIGood2.lean:0 
$ git diff --stat main...t/T2485; importers of Step5IIIGood*
touches only the two files:  2 files changed, 902 insertions(+)
importers: RBM3D/BA/Step5IIIGood2.lean 
$ import RBM3D + both modules + #assert_rbm_axioms (assert.lean), against import RBM3D alone (assert0.lean)
axiom audit: 14434 theorems, 4535 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
diff of the two outputs (premise scan): 2 lines, all in line 1 (declaration counts); error lines: 0
```
Narrative (1b):
- Verdict: every target delivered on `t/T2485` (no split: central 1,430 ≤ 1,950; 704 + 198 lines). Commits 40e6e696 (targets 1-3), 52d4df3e (target 4, instances), 10152ee4 (docs).
  `RBM3D.lean` and `Test/Axioms.lean` are not edited: the hub adds `import RBM3D.BA.Step5IIIGood` and `...Good2` at merge. Registry: none (the premise scan above is unchanged).
- Route as in (a). (ii), (iii): the sequence forms of `baKbound_holds` and `baEMn2ExpHK` become statements for every `u ∈ [s_n, t_n]` by `Step5IIIGood_uniform` (a violator sequence
  `τ_n ∈ [s_n, t_n]`; `τ_n < 1` by `EMn2BA_T0_lt_one`); (ii) is a deterministic `≺` (`Step5IIIGood_det_of_prec`: the bad set is `∅` or the space, of mass `1 > N^{-1}`).
- (iv)-(vi): the seven events are the `badSetAt` sets of `STAvgUgL`, `STLmaxUgL` (k = 2, 3, 4, 6), `STLKUgL` (k = 2), `STGdecayWgL`; they carry the union over `u`, so `G` (the complement of their
  union) does not depend on `u` and the private `lemDecCalEPrec_fixed` is not copied (`lemDecCalEPrec_union7` is: `Step5IIIGood_union7`).
- Constants: `q = N^{τ'/2} ≥ 32` eventually, `N^{τ'} = q²`; `Bctl ≤ 2(W^d(1-u))⁻¹` needs only `u < 1`, `L ≥ 1`; `ellT = 1` from `lam² ≤ 1 - u`; `ρ ≤ W^d` and `τ⁻¹ ≤ W^d` from `lam_sq_mul_pow_ge`.
  Floor index `D'' = D + τ'/𝔠` (the 1a table has `+ 1`; not needed: `q W^{-D''} ≤ W^{τ'/(2𝔠) - D - τ'/𝔠} ≤ W^{-D}`).
- Not used (greps above): entry-level bounds, `|E| < 2`, `M = mI`, `‖m‖ = 1`, `lam0 ≤ lam`/R1, any Step 1 name. No port from RBM1D or RBM2D. Copies from this repo: `lemDecCalEPrec_union7`
  (`Induction/LemDecCalEPrec.lean:705`, private there), `T2459_sz0_lam_le` (`t/T2459` @ 2a6ad6e0, `Probe/T2459Pins.lean`).
- Instances. Targets 1-3 have theirs in File 1 (CLAUDE.md §4 step 2: same file), target 4 and the composed instance in File 2. Deviation from ticket 5(c): target 2 is instanced through target 3, not at
  `n = 1`, `H = 0`: its matrix-part premise cannot be discharged there without computing 𝒦, and the window of (iii) is collapsed at `n = 1` ((a): 18.25 > 4). The example takes an eventual `n`
  (`flow_sz0`), `u = 1/2`, a sample `ω ∈ G` (`G ≠ ∅` since `P(Gᶜ) ≤ N^{-1} < 1`) and gives the matrix part at `D' = 30` with `J♯` recomputed. Target 1 is instanced at `n = 1`, `H = 0`.
  The four Steps 2-4 predicates stay hypotheses of the examples; the composed instance also takes `Step5IIIGood2_Edet 3`.
- Private stem copies, instance sections only: File 1 `Step5IIIGood_Mat`; File 2 `Step5IIIGood2_Scalar`, `_Matrix`, `_EdetConcl`, `_Edet` (= `T2482-check` `:155-195`); targets 2-4 carry the bundle inline. Imports beyond the ticket
  list: File 1 `BA/GreenSchur` (`BAflow_real`, `BAflow_lam0_window`); File 2 `Path/LemDecCalEwG` (`lossE2wG` in the Edet copy).

## (c) Verified Mathlib names (all compiled in this build)
`Real.rpow_add'`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_natCast`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.rpow_one`, `Real.rpow_two`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.rpow_le_rpow`,
`Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.mul_rpow`, `Real.inv_rpow`, `Real.exp_mul`, `Real.sqrt_eq_rpow`, `Real.sqrt_sq_eq_abs`, `Real.sqrt_le_sqrt`, `tendsto_rpow_atTop`, `Real.tendsto_log_atTop`, `tendsto_atTop_mono'`,
`Filter.Tendsto.eventually_ge_atTop`, `Filter.Eventually.exists`, `measure_union_le`, `measure_univ`, `ENNReal.one_le_ofReal`, `ENNReal.ofReal_mul`, `inv_anti₀`, `inv_lt_one_of_one_lt₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`,
`pow_le_pow_right₀`, `div_le_iff₀`, `Nat.pow_le_pow_right`, `Set.eq_univ_of_forall`, `Set.mem_ofPred_eq`, `Finset.le_sup'`, `le_of_eq_of_le`.
Deprecated here (warnings seen while writing; avoided): `dif_pos`/`dif_neg` (use `dite_true`/`dite_false` after `simp only [hv]`), `push_neg` (use `not_le.1`), `Set.mem_setOf_eq` (→ `Set.mem_ofPred_eq`). `import Mathlib` fails (no top-level `Mathlib.olean`): scratch files import project modules.

## (d) Open issues and paper-delta candidates
- T2485a (= design F2b): the good event carries the `J`-free decay (vi), `|(𝓛-𝒦)^{(2)}| ≤ W^{θd(Cd+1)} N^{τ'} (W^d(1-u))^{-2} e^{-θ√r} + W^{-D}`, from Steps 2 and 4 (`STLKUgL` k = 2 interpolated with `STGdecayWgL`), which the paper's stopping-time argument (`3_5:2364-2383`) does not list.
- T2485b: the Lean good event states `0 < ε`, `0 < 𝔡`, `0 < Cd` and `0 < θ < 1` (ticket note (2)(b), (c); (a): the min-inequality behind (vi) is false for `θ > 1`). T2485c: targets 3, 4 are at `d = 3` only (ticket answer (6)).
- Open: the `∃ G` form is not the measurable-preimage form U5d's `pathP` transfer needs (`pfStep5_goodMeas`; ticket answer (4)); `BAStep5IIIGoodThm` still takes the four Steps 2-4 predicates (owners T1/T1-BA, U3-BA; registered lines unchanged).
- When U5b-1/U5b-2 merge, the inline bundle texts equal `BAStep5IIIEScalar`/`EMatrix` by unfolding (the one-line bridge goes to U5d); the private copies are then redundant.
