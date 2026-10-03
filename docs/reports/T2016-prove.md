Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 02:20:36 UTC 2026

Notation: `ρ = W^ε`, `ratio = (g²+1−s)/(g²+1−t)`, `ℓ_t = min(max(g/√(1−t),1),L)`, `|a|` = periodic `l¹` distance, `Λ = 𝔡⁻¹`. Sources: `A_deterministic_estimates.tex:84–314`, `3_5_Loop_Hierarchy.tex:100–140, 328, 1444–1482, 1615–1700`, `7_8_light_weight.tex:1661`, `1_2_Intro_model_result.tex:1100–1185`, `RBM3D/Propagator/Pins.lean`, `RBM3D/Defs/Params.lean`.

### (i) Exponent table (d = 3 and general d ≥ 3)

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `d` | 3 (all `d ≥ 3`) | pins `3 ≤ d`; merged `propT` proves `d ≥ 2` | — |
| 2 | `Λ, g`; constants | `Λ=1, g=1/2`; pin constants `C(d,Λ[,κ,c])` before `L,g,t,m` | `0<g≤Λ`; merged `ThetaDecay…` put `C` after `g,m` (non-uniform in `g`) | (A): `g∈{1,.5,.1,.02,.005}` at L=9 gives r1≤1.001, r3≤1.663, r2≤4.178 |
| 3 | regime I `1−t ≥ g²` | `ℓ_t=1`; zero-mode `≤ 2L^{-d}×` first term at `K=0` | exp. decay at lattice scale | `L^{-d}=1/125` at L=5 |
| 4 | regime II `g²/L² ≤ 1−t ≤ g²` | `ℓ_t=g/√(1−t)∈[1,L]`, `ℓ_t²(1−t)=g²`; zero-mode ≤ first term at `K=ℓ_t` by `2^{d-1}(ℓ_t/L)^d` | `ℓ_t ≤ L` | instance `1−t=.1`: `ℓ_t=1.581`, ratio .072 ≤ .126 |
| 5 | regime III `g²/L^d ≤ 1−t ≤ g²/L²` | `ℓ_t=L`; zero-mode `∈[L^{2−d}/g², 1/g²]` overtakes the first term for `K ≳ K*=(L^d(1−t)/g²)^{1/(d−2)} ∈ [1,L]` | outside `lem:sum_decay` (`t ≤ 1−g²/L²`); inside `lem:sum_decay_nonzero`, `lem:propT`(ii) | — |
| 6 | regime IV `1−t < g²/L^d` | zero-mode `> 1/g²`, `Θ ≈` const | pins have no lower bound on `1−t`; checked at `t=1−g²/L³` in (B) | — |
| 7 | `(1−s)ℓ_s²` vs `g²+1−s` | `∈[1/2,1]` for `s ≤ 1−g²/L²` (`=g²` if `g²≥1−s`, else `ℓ_s=1`) | `(eq:1-sells2)` | instance .667 |
| 8 | `B_{t,0}ℓ_t²(1−t)` | max over grid (d=3) = 1.2333 | `≤ 3` (`Bparam_mul_ellT_sq_le`), needs `1−t ≥ g²/L²` | 2.4× |
| 9 | lattice sums | `Σ_{|x|≤R}(|x|+1)^{-(d-2)} ≍ R²`; `Σ_x(|x|+1)^{-(d-2)}e^{-c|x|/ℓ} ≍ ℓ²`; `Σ_{Z_L^d}(|x|+1)^{-(d-2)} ≤ C_dL²`: exponent 2, no log, every `d≥3` | ⇒ `Σ_b|Ξ| ≲ (1−s)ℓ_t²/(g²+1−t) ≍ (1−s)/(1−t)` | constants `C_d` (sphere sizes) |
| 10 | `ρ`, `R=ρℓ_s` | `W=10, ε=1/2`: `ρ=3.162`, `R=3.162` (57/125 sites) | `s≤t≤1−g²/L²`, `(1−t)/(1−s) ≥ W^{-1}`, `ε∈(0,1)`, `D>1` | `(1−t)/(1−s)=.2 ≥ .1` (2×); `t=.9 ≤ .99` |
| 11 | `(sum_res_1)`, n=2 | `ρ`-power `2(n−1)=2`; empirical `r1 ≤ 1.50` (all (A)) | `W^{C_nε}` (ρ-power) | candidate `C=2`: 1.3× |
| 12 | `(sum_res_2_NAL)`, n=2 | `ρ`-power `2(n−1)`; `ratio^{n−1}`; `r3 ≤ .79` (g≤.5), `1.66` (g=1, L=9) | same | candidate `C=2` |
| 13 | `(sumAzero)`, n=2 | `ρ`-power: paper `n+5`; my recount of `(eq:bddfA)`: `(n−2)+(d+1)−2(d−3)=n+5−d` (`=n+2=4` at d=3, excl. log); numerics `r2 ≤ 3.4` with `ρ⁴`; ρ-growth of the exact sup (L=9,g=.1): ×4.77 (ρ=2), ×30.7 (ρ=4), i.e. `ρ^{2.3–2.7}`. **At d=3 the constant grows like `log L`**: `Q2/ratio² = 2.25, 2.75, 3.37, 4.02` at `L=5,9,17,33` (slope ≈ 1 per `log L`); d=4 decreases (.94,.83,.80) | paper absorbs `log L ≤ W^ε` (`(eq:latticesum_d3)` text) ⇒ Lean pin needs `(1+log L)` (d=3) or the hypothesis `log L ≤ ρ`; `d≥4` none | `1+log L = 2.61,3.20,3.83,4.50 ≥` data (1.1–1.2×) |
| 14 | `(eq:latticesum_d3)` | `≤ C_d log L / R^{d−3}`; d=3: `S/log L` = 2.05→2.87, slope 3.90 (L 33→65) ⇒ `C_3 ≳ 4`; d=4: `S·R ≤ 1.75` (L≤25) | `1≤R≤L` | log only at d=3 (summand `~|b|^{-(2d-3)}`, shell `r^{d−1}`) |
| 15 | pin 6 range `|r| ≤ c|a|`, `c<1` | `(eq:Xibb)`: `|b_i−b_1| ≤ ρℓ_s` vs `|a_i−b_1| ≥ ρ²ℓ_s` ⇒ ratio `ρ^{-1}` | **needs `ρ ≥ 1/c`** (ρ≥2 for c=1/2); not in the paper | instance `ρ=3.16`: 1.58× |
| 16 | `lem:sum_decay_nonzero` | `‖Proj‖=2(1−L^{-d})≤2`; one-index `‖Proj U‖ ≤ 2.013` (L≤33), tested `g∈{.5,.1}`, `L≤33`, no `L^τ`/`≺`; needs `‖Proj Ξ‖ ≤ C(1−s)L²/g² ≤ C` (pin 8, row 9) | `1−g²/L² ≤ s ≤ t < 1`, `A ⊇ I_diff` | trivial bound `(1−s)/(1−t)=1089` at L=33 |
| 17 | same-sign index | `‖U‖ ≤ 1.09` (instance 1.093); pin 5s: `Σ_a|Θ| ≤ C_κ(1+g²Σe^{-c_κ|a|})` | `κ ≤ Im m`; `C5s` (c_κ=κ/2) = .80,.87,1.08,1.45 for κ=1,.5,.296,.1 | `C(d,Λ,κ)` |
| 18 | `lem:propT` `(TTT2)` | `C_d` uniform in `L,g,u,t`; sup_L numeric `260.6` (L=97), `254.3` (L=129): finite-size growth saturates | (i) `1−u ≥ 1−t ≥ g²/L²` or (ii) `1−t ≤ 1−u ≤ g²/L²`; mixed `1−t<g²/L²<1−u` not covered | instance `(u,t)=(.5,.9)`: 8.98 |
| 19 | `claim:TTk` | `Ψ_t²ℓ² ≤ 3Λ²W^{-d}/(1−t)` for `ℓ ≤ Λℓ_t`, `Λ=(log W)^{10}` | `1−t ≥ g²/L²`, `k ≥ 2`; `(eq:TtTt)` needs `|x−α|∨|y−α| ≤ ℓ` (false otherwise: `x=y`, both ≫ ℓ) | row 8: 1.23 vs 3 |
| 20 | pins 5, 5s, 6, 7, 8 (external) | constants (c=.25, c_κ=.5, c=1/2): `C5 ≤ 1.43` (L→65, increments .118,.047,.025), `C5s ≤ .99`, `C8 ≤ 1.25`, `C6 ≤ .99`, `C7 ≤ 2.77` | `t` up to `1−g²/L³` | no counterexample in (B) |
| 21 | `d=2` exponents (RBM2D at `c9a24cf`, read via `git show`) | `(1+log L)` factors: `XiBounds.lean:78,84,94,100,195,199`; `LatticeSums.lean:22–27,62,77` (`√(5+4 log L)`); `KernelExpand.lean:30,47,56,69` (`(1+log L)^{k−1}K^{2(k−1)}`); `Case4.lean:49,57–58` (`((1+log L)L²)^k`); `Case5.lean:56,68–69`; `min 1 (L²(1−t))` in `XiBounds:78,84` | d≥3: row 9 removes all logs except row 13/14 at d=3 | `../RBM2D` HEAD is `9e0f275`, 9 commits past `c9a24cf` (`Evolution/` diff: 24 files, +713 −3584) |

### (ii) One nondegenerate instance (d=3, L=5, g=1/2, t=9/10, s=1/2, W=10, ε=1/2, D=2, n=2, m=i, κ=1/2, Λ=1)

Commands (python3/numpy, exact `Θ` by Fourier sum; scripts in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad`):
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad && python3 ek_instance.py`
```
hypotheses: [3<=d:True] [3<=L:True] [0<g<=Lam:True] [0<=s<=t<1:True] [t<=1-g2/L2:True] [(1-t)/(1-s)>=1/W:True] [eps in(0,1),D>1:True] [|m|=1,kap<=Im m:True] [regime II g2/L2<=1-t<=g2:True] [l_s<=l_t<L:True] [nonzero window 1-g2/L2<=.995<=.999<1:True]
l_s=1.000 l_t=1.581 R=W^eps l_s=3.162 (#cluster sites 57/125) ratio=2.1429 (1-s)l_s^2/(g2+1-s)=0.667 B_t0=2.937 zero-mode term=0.080
alt(+,-): (Ndecay) ||U2||=25.0000 <= ((1-s)/(1-t))^2=25.0 | (sum_res_1) sup_A||UA||=16.809, (l_t/l_s)^2 ratio^2=11.480, /(rho^2*.)=0.146 | (NAL, only sigma=(+,+)) /(rho^2 ratio)=0.784
same(+,+): (Ndecay) ||U2||=1.1951 <= ((1-s)/(1-t))^2=25.0 | (sum_res_1) sup_A||UA||=1.187, (l_t/l_s)^2 ratio^2=11.480, /(rho^2*.)=0.010 | (NAL, only sigma=(+,+)) /(rho^2 ratio)=0.055
(sumAzero, alt) explicit A=f(b2-b1), f=delta_0-1_(|z|<=1)/7: sum f=1.1e-16 max|f|=0.857 -> ||UA||=1.3402 (0.292 ratio^2); worst real sum-zero A in cluster: 11.562 = 2.518 ratio^2 = 0.0252 rho^4 ratio^2 (1+log L=2.609)
pins (+,-): C5(c=.25)=0.632  C5s(c=.5)=n/a(only sigma1=sigma2)  C8=0.622
pins (+,+): C5(c=.25)=0.257  C5s(c=.5)=0.605  C8=0.263
nonzero window s'=.995,t'=.999: one-index ||Proj U||: alt=1.993 same=1.982 (<=2 = ||Proj||) ; ||U|| same (index not in A)=1.001 ; trivial (1-s')/(1-t')=5.0
propT (u,t)=(0.5,0.9) regime (i): max_x (1-u) sum_c T_u T_t/T_t = 8.977
```
`python3 ek_preflight.py` (grid: L∈{5,9,17}, g∈{1/2,1/10}, t∈{.5,1−g²,1−g²/L²}, s∈{0,t/2}; `t=1−g²/L²` is the closed edge of the hypothesis `t ≤ 1−g²/L²`):
```
== (A) n=2, d=3, exact Theta; s in {0,t/2}, t in {.5,1-g2,1-g2/L2}, rho in {1,2,4}, m=i: r1=sup||UA||/(rho^2 (l_t/l_s)^2 ratio^2), r3=NAL sup/(rho^2 ratio), r2=sup over real sum-zero A /(rho^4 ratio^2) ==
   L= 5: max_g r1=1.495  max_g r3=0.787  r2(g=.5)=2.248 r2(g=.1)=1.349
   L= 9: max_g r1=1.085  max_g r3=0.787  r2(g=.5)=2.752 r2(g=.1)=1.543
   L=17: max_g r1=1.085  max_g r3=0.787  r2(g=.5)=3.370 r2(g=.1)=1.765
   uniform in g (L=9): g=1.0: (r1,r3,r2)=1.000,1.663,4.178  g=0.02: (r1,r3,r2)=1.001,0.464,1.478  g=0.005: (r1,r3,r2)=1.000,0.463,1.475
   sumAzero at rho=1, t=1-g^2/L^2, s=0, Q2/ratio^2 vs log L:
   d=3 g=0.5: L=5:2.248  L=9:2.752  L=17:3.370  L=33:4.021   (log L = 1.61,2.20,2.83,3.50)
   d=4 g=0.5: L=5:0.938  L=9:0.834  L=13:0.802
   d=3 g=0.1: L=5:1.349  L=9:1.543  L=17:1.765  L=33:1.976   (log L = 1.61,2.20,2.83,3.50)
   d=4 g=0.1: L=5:0.406  L=9:0.297  L=13:0.255
== (B) pins as external hypotheses, d=3, m=i, t in {0,.5,1-g2,1-g2/L2,1-g2/L3}, both sign pairs, all a: C5=|Th|/(B e^{-.25|a|/l_t}), C5s=|Th|/(1_{a=0}+g2 e^{-.5|a|}), C8=|Th0|(g2+1-t)(|a|+1)
   L= 5  g=0.5: C5=1.238 C5s=0.800 C8=1.240 | g=0.1: C5=1.166 C5s=0.990 C8=1.002
   L=17  g=0.5: C5=1.356 C5s=0.800 C8=1.250 | g=0.1: C5=1.363 C5s=0.990 C8=1.010
   L=33  g=0.5: C5=1.403 C5s=0.800 C8=1.250 | g=0.1: C5=1.407 C5s=0.990 C8=1.010
   L=65  g=0.5: C5=1.428 C5s=0.800 C8=1.250 | g=0.1: C5=1.430 C5s=0.990 C8=1.010
   C5s kappa-dependence (g=.5, L=17, m=e^{i th}, kappa=sin th, c_kappa=kappa/2, all t above): kappa=1.000: 0.80  kappa=0.500: 0.87  kappa=0.296: 1.08  kappa=0.100: 1.45
   L= 5 (c=1/2, |r|<=|a|/2)  g=0.5: C6=0.845 C7=2.546 | g=0.1: C6=0.452 C7=1.356
   L=17 (c=1/2, |r|<=|a|/2)  g=0.5: C6=0.986 C7=2.768 | g=0.1: C6=0.473 C7=1.176
== (C) lem:propT (TTT2), d=3, g=.5, (u,t)=(0,.5), max_x (1-u) sum_c T_u T_t/T_t : saturates (finite-size growth only)
   L=5:12.7  L=9:32.7  L=17:79.6  L=33:160.1  L=65:241.4  L=97:260.6  L=129:254.3
   max B_t0 l_t^2 (1-t) over grid (regime 1-t>=g2/L2, d=3) = 1.2333  (<=3)
== (D) lem:sum_decay_nonzero / sum_Ndecay, one-index operators, d=3 ==
   L= 5  g=0.5: ||ProjU||alt=2.005 ||ProjU||same=1.984 ||U||alt=25.0(=max (1-s)/(1-t)=25.0) | g=0.1: ||ProjU||alt=2.000 ||ProjU||same=1.984 ||U||alt=25.0(=max (1-s)/(1-t)=25.0)
   L=17  g=0.5: ||ProjU||alt=2.012 ||ProjU||same=2.000 ||U||alt=289.0(=max (1-s)/(1-t)=289.0) | g=0.1: ||ProjU||alt=2.002 ||ProjU||same=2.000 ||U||alt=289.0(=max (1-s)/(1-t)=289.0)
   L=33  g=0.5: ||ProjU||alt=2.013 ||ProjU||same=2.000 ||U||alt=1089.0(=max (1-s)/(1-t)=1089.0) | g=0.1: ||ProjU||alt=2.002 ||ProjU||same=2.000 ||U||alt=1089.0(=max (1-s)/(1-t)=1089.0)
   sum_Ndecay: max ||U^(1)||(1-t)/(1-s) over grid = 1.000000  (<=1)
== (E) (eq:latticesum_d3), c=1, ell=L, a1=0: S=max_{a2} sum_{b:|a1-b|^|a2-b|>R} e^{-|a1-b|/L}/(|a1-b|^{d-2}|a2-b|^{d-1}) ==
   d=3,R=1: L=9:S/logL=2.047  L=17:S/logL=2.405  L=33:S/logL=2.671  L=65:S/logL=2.870   slope dS/dlogL (33->65) = 3.90
   d=4,R=1,2,4: L=9:S*R=1.32/1.05/0.58  L=17:S*R=1.62/1.46/1.12  L=25:S*R=1.75/1.66/1.39
```
External-hypothesis limit computation (TEAM §8 lesson 14): block (B) above evaluates pins 5, 5s, 8 up to `L=65` and pins 6, 7 up to `L=17`, with `t` down to `1−g²/L³`, both sign pairs; ratios stay bounded and the `L`-increments of `C5` shrink. `m=i` only (and the κ line of (B)).

### Verdicts
- `lem:sum_Ndecay`: PASS (`‖U‖ = (1−s)/(1−t)` per index, equality for `(+,−)`; hypotheses hold at the instance).
- `lem:sum_decay` `(sum_res_1)`, `(sum_res_2_NAL)`, `(deccA0)`: PASS (r1 ≤ 1.50, r3 ≤ 1.66, no growth in L).
- `lem:sum_decay` `(sumAzero)`, `(sum_res_2)`: PASS with a required statement shape: at `d=3` the deterministic bound carries `(1+log L)` (data grow like `log L`) or an explicit `log L ≤ ρ`; and pin 6 needs `ρ ≥ 1/c`. Candidates `T2016a` (log L, d=3 only; paper hides it in `W^{Cε}`), `T2016b` (`ρ ≥ 1/c` for `(prop:BD1)`).
- `lem:sum_decay_nonzero`: PASS (`‖Proj U‖ ≈ 2`, no `≺`/`L^τ` loss needed with pin 8).
- `lem:propT`: PASS (finite constant; mixed regime not covered by the paper, candidate `T2016c`, no downstream use found).
- `claim:TTk`: PASS (`Ψ²ℓ²` form; range hypothesis of `(eq:TtTt)`, candidate `T2016d`).
- Overall: PASS.

## (b) Script output — probe `RBM3D/Probe/T2016Pins.lean` (branch `t/T2016`, base `110a9a2`); RBM2D read-only at `c9a24cf`; probe Appendices A–C hold the full lists and every script source
### b1 Build, axioms, forbidden tokens
Sat Oct  3 03:57:10 UTC 2026
$ git log --oneline 110a9a2..HEAD; git status --short | wc -l
c961e62 T2016: probe RBM3D/Probe/T2016Pins.lean (EK-D1: pins, n = 2 skeleton, BA reuse witness, instances, appendices)
0
$ lake build RBM3D.Probe.T2016Pins 2>&1 | grep -E "^(warning|error)|Build completed"
Build completed successfully (2544 jobs).
$ lake env lean RBM3D/Probe/T2016Pins.lean > out.txt 2>&1; echo exit=$?; tail -2 out.txt
exit=0
'RBM.EKPropT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKTTk' depends on axioms: [propext, Classical.choice, Quot.sound]
$ awk (all "depends on axioms" lines of out.txt)
axiom lines: 27 ; exactly [propext, Classical.choice, Quot.sound]: 27 ; other messages: 0
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2016Pins.lean
0
### b2 The pins and the vocabulary (statements extracted from the probe; `Λ` = `𝔡⁻¹` except in `EKTTk`; PT pins are antecedents)
Sat Oct  3 03:57:29 UTC 2026
$ awk (the vocabulary and the pins, joined, wrapped at 215; docstrings in the file)
 noncomputable def EKsgn {n : ℕ} (m : ℂ) (σ : Fin n → Bool) : Fin n → ℂ := fun i => PropSpin m (σ i)
 def EKFastDecay {d L n : ℕ} (g s W ε D : ℝ) (A : (Fin n → Zd d L) → ℂ) : Prop := ∀ a : Fin n → Zd d L, (∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (a i - a j) : ℝ)) → ‖A a‖ ≤ W ^ (-D)
 def EKSumZero {d L n : ℕ} [NeZero L] (A : (Fin n → Zd d L) → ℂ) : Prop := ∀ i₀ : Fin n, i₀.val = 0 → ∀ x : Zd d L, ∑ b ∈ Finset.univ.filter (fun b : Fin n → Zd d L => b i₀ = x), A b = 0
 def EKSumNdecay (d n : ℕ) : Prop := 3 ≤ d → 2 ≤ n → ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin n → Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ A : (Fin n → Zd d L) → ℂ, ‖UN d L g (EKsgn m 
σ) s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖
 def EKSumDecay1 (d n : ℕ) (Λ : ℝ) : Prop := Prop5Decay d Λ → 3 ≤ d → 2 ≤ n → 0 < Λ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → ∀ s t 
: ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ, EKFastDecay g s W ε D A → ‖UN d L g (EKsgn m σ) s t A‖ ≤ W ^ (C * ε) * 
(ellT L g t ^ 2 / ellT L g s ^ 2) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)
 def EKSumDecayNAL (d n : ℕ) (Λ κ : ℝ) : Prop := Prop5Decay d Λ → Prop5Short d Λ κ → 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 
1 → 1 < D → 4 ≤ W ^ ε → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, (∃ k, σ k = σ (finRotate n k)) → ∀ A : (Fin n → Zd d L) → 
ℂ, EKFastDecay g s W ε D A → ‖UN d L g (EKsgn m σ) s t A‖ ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (n - 1) * ‖A‖ + W ^ (-D + C)
 def EKSumDecay2 (d n : ℕ) (Λ κ : ℝ) : Prop := Prop5Decay d Λ → Prop5Short d Λ κ → Prop6Diff1 d Λ κ (1 / 2) → 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D 
: ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, ∀ A : (Fin 
n → Zd d L) → ℂ, EKFastDecay g s W ε D A → EKSumZero A → ‖UN d L g (EKsgn m σ) s t A‖ ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)
 def EKSumDecayNonzero (d n : ℕ) (Λ κ : ℝ) : Prop := Prop5Short d Λ κ → Prop8ZeroMode d Λ κ → 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ s t : ℝ, 0 ≤ s → 1 - 
g ^ 2 / (L : ℝ) ^ 2 ≤ s → s ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, ∀ A : Finset (Fin n), (∀ i, σ i ≠ σ (finRotate n i) → i ∈ A) → ∀ 𝒜 : (Fin n → Zd d L) → ℂ, ‖zeroModeSet d L A (UN d L g 
(EKsgn m σ) s t 𝒜)‖ ≤ C * ‖𝒜‖
 def EKPropT (d : ℕ) : Prop := 3 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L] (g u t : ℝ), 0 < g → 0 ≤ u → u ≤ t → t < 1 → (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) → ∀ a b : Zd d L, ∑ c : Zd d L, 
tailT d L g u (zdistD d L (a - c)) * tailT d L g t (zdistD d L (c - b)) ≤ C / (1 - u) * tailT d L g t (zdistD d L (a - b))
 def EKTTk (d n : ℕ) : Prop := 3 ≤ d → 2 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) → ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ (D : Finset (Zd d 
L)) (a : Zd d L), (∀ α ∈ D, (zdistD d L (a - α) : ℝ) ≤ ℓ) → ∀ x y : Fin n → Zd d L, ∑ α ∈ D, ∏ i, (sfT d L W g t (min (zdistD d L (x i - α) : ℝ) ℓ) * sfT d L W g t (min (zdistD d L (y i - α) : ℝ) ℓ)) ≤ C * (Λ ^ 2 * 
((W ^ d)⁻¹ / (1 - t))) * (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistD d L (x i - y i) : ℝ) ℓ))
### b3 Skeleton and compiled nonempty instances (d=3, L=5, g=1/2, Λ=1, κ=1/2, m=i, n=2, s=1/2, t=9/10, W=25, ε=1/2 (W^ε=5 < torus diameter 6), D=2; nonzero window s=.995, t=.999; `ekA0=δ₀`, `ekAz=δ₀⊗(δ₀−δ_e)`, e=(1,0,0))
Sat Oct  3 03:57:29 UTC 2026
$ awk (ekSumDecay1_two and the instances ekInst*, statements joined, wrapped at 215)
 theorem ekSumDecay1_two (d : ℕ) (Λ : ℝ) : EKSumDecay1 d 2 Λ
 ekInstNdecay : ‖UN 3 5 (1 / 2) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) ekA0‖ ≤ ((1 - 1 / 2) / (1 - 9 / 10)) ^ 2 * ‖ekA0‖
 ekInstDecay1 (h5 : Prop5Decay 3 1) : ∃ C : ℝ, 0 < C ∧ ‖UN 3 5 (1 / 2) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) ekA0‖ ≤ (25 : ℝ) ^ (C * (1 / 2)) * (ellT 5 (1 / 2) (9 / 10) ^ 2 / ellT 5 (1 / 2) (1 / 2) ^ 2) 
* (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2 * ‖ekA0‖ + (25 : ℝ) ^ (-2 + C)
 ekInstNAL (h : EKSumDecayNAL 3 2 1 (1 / 2)) (h5 : Prop5Decay 3 1) : ∃ C : ℝ, 0 < C ∧ ‖UN 3 5 (1 / 2) (EKsgn Complex.I ![true, true]) (1 / 2) (9 / 10) ekA0‖ ≤ (25 : ℝ) ^ (C * (1 / 2)) * (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 
2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ (2 - 1) * ‖ekA0‖ + (25 : ℝ) ^ (-2 + C)
 ekInstDecay2 (h : EKSumDecay2 3 2 1 (1 / 2)) (h5 : Prop5Decay 3 1) (h6 : Prop6Diff1 3 1 (1 / 2) (1 / 2)) : ∃ C : ℝ, 0 < C ∧ ‖UN 3 5 (1 / 2) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) ekAz‖ ≤ (25 : ℝ) ^ (C * 
(1 / 2)) * (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2 * ‖ekAz‖ + (25 : ℝ) ^ (-2 + C)
 ekInstNonzero (h : EKSumDecayNonzero 3 2 1 (1 / 2)) (h8 : Prop8ZeroMode 3 1 (1 / 2)) : ∃ C : ℝ, 0 < C ∧ ‖zeroModeSet 3 5 Finset.univ (UN 3 5 (1 / 2) (EKsgn Complex.I ![true, false]) (995 / 1000) (999 / 1000) 
ekA0)‖ ≤ C * ‖ekA0‖
 ekInstPropT : ∃ C : ℝ, 0 < C ∧ ∑ c : Zd 3 5, tailT 3 5 (1 / 2) (1 / 2) (zdistD 3 5 (0 - c)) * tailT 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (c - ekE)) ≤ C / (1 - 1 / 2) * tailT 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (0 - ekE))
 ekInstTTk : ∃ C : ℝ, 0 < C ∧ ∑ α ∈ Finset.univ.filter (fun α : Zd 3 5 => (zdistD 3 5 (0 - α) : ℝ) ≤ 1), ∏ i, (sfT 3 5 25 (1 / 2) (9 / 10) (min (zdistD 3 5 (![0, ekE] i - α) : ℝ) 1) * sfT 3 5 25 (1 / 2) (9 / 10) 
(min (zdistD 3 5 (![ekE, 0] i - α) : ℝ) 1)) ≤ C * (1 ^ 2 * (((25 : ℝ) ^ 3)⁻¹ / (1 - 9 / 10))) * (PsiT 3 5 25 (1 / 2) (9 / 10) ^ (2 - 2) * ∏ i, sfT 3 5 25 (1 / 2) (9 / 10) (min (zdistD 3 5 (![0, ekE] i - ![ekE, 0] 
i) : ℝ) 1))
### b4 Name clash, ports (no RBM1D/RBM2D text copied)
Sat Oct  3 03:57:29 UTC 2026
$ names=$(public theorem/def names of the probe); echo $names | wc -w; for n in $names; do grep -rlw --include="*.lean" "$n" RBM3D RBM3D.lean | grep -v Probe; done | wc -l
48
0
$ python3 diffcopy.py <worktree>   (the only copied text is from merged RBM3D files; nothing from RBM1D/RBM2D; RBM2D read at c9a24cf only)
ek_norm_XiKer_apply_le (probe lines 225-347) vs merged norm_XiKer_apply_le (SumDecay.lean lines 386-512): 4 differing lines, all removals: -  obtain ⟨Cd, hCd, cd, hcd, hbd⟩ := hdecay hd h | -  -- constants: the zero-mode absorption, the s | -  refine ⟨Cd * (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k | -    cd, hcd, ?_⟩
ek_sum_ball_norm_XiKer_le (probe lines 368-447) vs merged sum_ball_norm_XiKer_le (SumDecay.lean lines 550-631): 2 differing lines, all removals: -  obtain ⟨C₀, hC₀, c, hc, hbd⟩ := norm_XiKer_ap | -  refine ⟨4 * C₀ * ballC k, mul_pos (by positiv
skeleton size (declaration with docstring): new = 24 + 28 + 7 + 24 + 25 + 187 = 295 lines; copied = 137 + 97 = 234 lines
### b5 Item 1, inventory: merged `Kernel/*` (key rows; the 91 rows are probe Appendix A), importers, RBM2D `Evolution/*`
Sat Oct  3 03:57:29 UTC 2026
file | public decls | theorems | with an old propagator Prop | with ∃-constants | with a loss factor
Evolution.lean | 35 | 24 | 3 | 3 | 2
PropT.lean | 43 | 36 | 0 | 1 | 2
SumDecay.lean | 13 | 11 | 3 | 3 | 5
key rows (old Props, ∃-constants, or named in the ticket):
Evolution.lean:114 norm_uKer_le | old:- | consts:explicit | loss:none
Evolution.lean:131 norm_UN_apply_le | old:- | consts:explicit | loss:none
Evolution.lean:157 norm_UN_le | old:- | consts:explicit | loss:none
Evolution.lean:445 exists_norm_uKer_same_le | old:ThetaDecayShort | consts:g,m < C < L,s,t | loss:none
Evolution.lean:520 exists_norm_projMat_mul_uKer_le | old:ThetaZeroMode | consts:g,μ < C < L,s,t | loss:L^τ
Evolution.lean:629 norm_zeroModeSet_UN_le | old:ThetaDecayShort,ThetaZeroMode | consts:g,m < C < L,s,t | loss:L^τ
PropT.lean:409 propT | old:- | consts:- < C < g,L,t,u | loss:none
PropT.lean:1056 key_T_reduce_absorbed | old:- | consts:explicit | loss:Λ²
SumDecay.lean:149 latticesum_d3 | old:- | consts:explicit | loss:log
SumDecay.lean:376 norm_XiKer_apply_le | old:ThetaDecay | consts:g,μ < C < L,s,t | loss:none
SumDecay.lean:540 sum_ball_norm_XiKer_le | old:ThetaDecay | consts:g,μ < C < L,s,t | loss:Λ²
SumDecay.lean:667 sum_prod_norm_XiKer_le | old:ThetaDecay | consts:g,μ < C < L,s,t | loss:Λ²
91 public Kernel declarations; files outside Kernel/ importing a Kernel module: RBM3D/Loop/PureLoop.lean, RBM3D.lean; files mentioning a Kernel declaration (comments stripped): none
Sat Oct  3 03:57:30 UTC 2026
$ python3 inv_rbm2d.py docs/reports/T2002-portmap.md   (commits: c9a24cf = ticket, 0c1330a = RBM2D after its dead-code deletion)
file | lines c9a24cf | kept 0c1330a | class (T2002 portmap line) | d=2 tokens (log, L², Z2/zdist2 occurrences at c9a24cf) | paper labels (this paper, portmap)
Defs.lean | 219 | 145 | b (371) | log:0 L2:2 Z2:23 | lem_GbEXP@3_5:14; Main_DEL_COND@1_2:359; deccA0@3_5:1634; lem_decayLoop@3_5:1126; res_decayLK@3_5:1128; sum_re
Bridge.lean | 461 | 425 | b (359) | log:34 L2:8 Z2:4 | sum_res_1@3_5:1639
KernelExpand.lean | 612 | 581 | b (373) | log:36 L2:12 Z2:110 | lem:sum_decay@3_5:1632; sum_res_1@3_5:1639
XiBounds.lean | 783 | 734 | b (382) | log:37 L2:20 Z2:198 | lem:sum_decay@3_5:1632
LatticeSums.lean | 92 | 82 | b (374) | log:4 L2:0 Z2:29 | 
Case3Defs.lean | 182 | 147 | b (361) | log:0 L2:0 Z2:16 | lem_GbEXP@3_5:14; GijGEX@3_5:24
Case3.lean | 4275 | 3828 | b (360) | log:129 L2:64 Z2:366 | lem:sum_decay@3_5:1632; lem:main_ind@1_2:1256
Case4.lean | 1891 | 1732 | b (362) | log:72 L2:49 Z2:353 | lem:sum_decay@3_5:1632; sumAzero@3_5:1655
Case5.lean | 1562 | 1439 | b (363) | log:73 L2:54 Z2:289 | lem:sum_decay@3_5:1632
Clt*+FarEntry (Step 5, ST-4): 8 files | 6695 | 5988 | class b | not this gate
MLExp*+Step61 (Step 6, ST-5): 7 files | 7853 | 6846 | class c | not this gate
### b6 Item 2, gate boundary (ST-1/2 = Steps 1–2, ST-3 = Steps 3–4 (3_5:900–1935), ST-4 = Step 5, ST-5 = Step 6, LW = §7)
Sat Oct  3 03:57:31 UTC 2026
$ python3 inv_boundary.py docs/reports/T2001-coverage.md
# | paper label | TeX loc | gate | Lean class | consumers (script, ≤ 6): label[gate]
77 | DefTHUST | 3_5:109 | EK | iii | lem:DIfREP[ST=ST-1/2], lem:newKLK[ST=ST-1/2], Def:QtPt[ST=ST-3], lem_+Q[ST=ST-3], lem:STOeq_Qt[ST=ST-3], lem: newPQ[ST=ST-3] …(+4)
81 | def: TTfunc | 3_5:311 | EK | i | lem:newKLK[ST=ST-1/2], lem: EWGn2_N[LW], ygdhmsgq0[ST=ST-1/2], [sec 7_8:1 Estimation of the light-weight ter][LW]
82 | lem:propT | 3_5:328 | EK | i | def: TTfunc[EK], lem:newKLK[ST=ST-1/2], ygdhmsgq0[ST=ST-1/2], [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2][ST-4], lem:LW_moment_exp_near[LW]
111 | def;zero_mode_remove | 3_5:1444 | EK | i | [sec 3_5:1935 Step 5: Pointwise estimate for (cL][ST-4], [sub 3_5:2251 The case g2/Ld leq 1-t leq 1-s leq][ST-4], [Step6-proof: proof@6:93][ST-5], lem:sum_decay_nonzero[EK]
114 | lem:sum_Ndecay | 3_5:1620 | EK | i | [Step3-proof: 3_5:1435][ST-3], TailtoTail[ST=ST-4], [Step6-proof: proof@6:93][ST-5], [sub A:84 Proofs of evolution kernel estimat][EK(proof)]
115 | lem:sum_decay | 3_5:1632 | EK | iv | lem_decayLoop[ST=ST-3], lem:STOeq_NQ[ST=ST-3], Def:QtPt[ST=ST-3], lem_+Q[ST=ST-3], lem:STOeq_Qt[ST=ST-3], [Step3-proof: 3_5:1435][ST-3] …(+2)
116 | lem:sum_decay_nonzero | 3_5:1666 | EK | iii | [Step3-proof: 3_5:1435][ST-3], lem: newPQ[ST=ST-3], lem:STOeq_Qt_nonzero[ST=ST-3], [Step6-proof: proof@6:93][ST-5], [sub A:84 Proofs of evolution kernel estimat][EK(proof)]
148 | claim:TTk | 7_8:1661 | EK | i | lem:LW_moment_exp_near[LW]
EK (deterministic kernel estimates, this gate): DefTHUST, `def;zero_mode_remove`, `def: TTfunc`, `lem:propT`, `claim:TTk`, `lem:sum_Ndecay`, `lem:sum_decay`, `lem:sum_decay_nonzero`, `(eq:latticesum_d3)`, `(eq:decompUalt)`–`(eq:Xibb)`. Not EK: stochastic use in ST-3 (`lem_decayLoop`, `lem:STOeq_NQ`, `lem:STOeq_Qt`, `lem:STOeq_Qt_nonzero`, `lem_+Q`, `Def:QtPt`, `lem: newPQ` (Ward expansion of `Q^{(A)}∘𝓛`, 3_5:1482; its `𝓚` half is KL)), ST-4 (`lem;CLT`, 3_5:2173), ST-5 (6:93), LW (`lem:LW_moment_exp_near`); `(deccA0)` for the tensor is supplied by the stochastic layer (3_5:1153), the EK pins are applied ω-by-ω.
### b7 Item 3, extreme inputs (a literal `W^{Cε}` has no lower bound on `W^ε`; `Q1/(q r²)` = sup‖UA‖/((ℓ_t/ℓ_s)²·ratio²‖A‖) over windows `< ρℓ_s`)
Sat Oct  3 03:57:31 UTC 2026
$ python3 rho2.py   (ek_lib.py of section (a): exact Theta by Fourier sum)
L g s t: Q1/(q r^2) at rho = 1.0001, 4, 10, 30 and the exponent log(Q1/(q r^2))/log(rho) (rho = 4, 10, 30)
L=5 g=0.1 s=0.0 t=0.99960: 1.495 12.110 26.507 26.507  | C_needed: 1.80 1.42 0.96
L=5 g=0.5 s=0.0 t=0.99000: 1.005 7.968 17.306 17.306  | C_needed: 1.50 1.24 0.84
L=9 g=0.1 s=0.0 t=0.99988: 0.788 7.065 72.466 81.377  | C_needed: 1.41 1.86 1.29
L=9 g=0.5 s=0.25 t=0.50000: 1.065 1.248 1.266 1.266  | C_needed: 0.16 0.10 0.07
$ python3 n3check.py
n=3, d=3, L=5, t=1-g^2/L^2 (g=.5: t=.99), s=0, 8 offset triples a; S = sup||UA||; per rho = 1.0001, 2, 4: S/(q r^3) [sum_res_1] and S/r^2 [NAL, rho^C allowed]
g=0.5 s=0.0 t=0.99000 sigma=++-  q=25.0 r=4.81 |   0.020   2.406 |   0.020   2.406 |   0.719  86.378
g=0.5 s=0.0 t=0.99000 sigma=+++  q=25.0 r=4.81 |   0.000   0.043 |   0.000   0.043 |   0.001   0.077
g=0.1 s=0.0 t=0.99960 sigma=++-  q=25.0 r=97.12 |   0.000   0.978 |   0.000   0.978 |   0.020  49.623
g=0.1 s=0.0 t=0.99960 sigma=+++  q=25.0 r=97.12 |   0.000   0.000 |   0.000   0.000 |   0.000   0.000
Other pins, extreme tried (numbers are in section (a)): `EKSumNdecay` t→1: one-index ‖U‖ = (1−s)/(1−t) = 25, 289, 1089 at L=5, 17, 33 ((a) block D, equality), n=2 instance ‖U²‖ = 25.0 = ((1−s)/(1−t))² ((a)(ii)); `EKSumDecay1` g→0.005 (L=9): r1 ≤ 1.001, L=17: ≤ 1.085 ((a) rows 2, 11); `EKSumDecayNAL` g=1, L=9: r3=1.663, g ≤ 1/2: ≤ .79; `EKSumDecay2` L=5→33: Q2/ratio² = 2.25→4.02, growing like log L (d=4, L=5→13: .94→.80) ⇒ hypothesis `log L ≤ W^ε`; `EKSumDecayNonzero` g=.1, L=33: ‖Proj U‖=2.002 (‖Proj‖ ≤ 2); `EKPropT` L=97, 129: sup 260.6, 254.3 (saturates); `EKTTk`: B_{t,0}ℓ_t²(1−t) ≤ 1.2333 ≤ 3. First column above: 1.495 > 1 at ρ=1.0001 (L=5, g=.1, s=0, t=1−g²/L²), so the literal display is false there; for ρ ≥ 4 the exponent needed is ≤ 1.86. The n=3 table (`n3check.py`, all `σ` are non-alternating for odd n): S/(q r³) ≤ 0.72 and S/r² = 86 at ρ=4 (≈ ρ^{3.2}, `C_3 ≈ 4`): no violation of `(sum_res_1)`, `(sum_res_2_NAL)` (L=5 only; not a proof). Not compiled (exact Θ has no closed form).
### b8 Items 3 and 5, status of each pin against merged `main`, and route (RBM2D file:line at `c9a24cf`; lines are estimates)
27/27 cited file:line pairs of the report tables start the named declaration
$ python3 chk21.py   (section (a) row 21 against `git show c9a24cf:`)
row 21 of (a): 19/19 cited line ranges contain `log` or `min 1 ((L : ℝ) ^ 2`; XiBounds 8/8; LatticeSums 3/3; KernelExpand 4/4; Case4 2/2; Case5 2/2
| pin | merged `main` | RBM2D source | d ≥ 3 change | lines / risk |
|---|---|---|---|---|
| `EKSumNdecay` | PROVED: `Evolution.lean:157 norm_UN_le` (no old Prop, no constant); compiled `ekSumNdecay_holds` | `Path/UBounds.lean:480 sumNdecay` | none (any d, n) | 0 / none |
| `EKPropT` | PROVED: `PropT.lean:409 propT`, d ≥ 2 (`ekPropT_holds`) | `Path/TailSums.lean:505 convTailT` | none | 0 / none |
| `EKTTk` | PROVED after a bridge: `PropT.lean:1056 key_T_reduce_absorbed` (`≺`→`Λ²`, `η_t`→`1−t`, `ℓ ≥ 1`; `ekTTk_holds`, C=3·keyC) | none | — | 0 (+EK-6) / none |
| `(eq:latticesum_d3)` | PROVED: `SumDecay.lean:149` (`latC k·log L/R^k`, d=k+3) | `LatticeSums.lean:22–27 expInvSum` (`√(5+4 log L)`) | log only at d=3 | 0 / none |
| `EKSumDecay1` | INGREDIENTS only, old `ThetaDecay`, C after `g`: `SumDecay.lean:376, 540, 667`; skeleton here: n=2 from `Prop5Decay`, uniform in g (295 new + 234 copied lines, b4) | `KernelExpand.lean:93 sum_prod_anchor_le`, `:370 core_bound`, `:472 ugenGenExplicit`; `XiBounds.lean:435 xiEntryBound`, `:497 xiRowBound` | no `(1+log L)^{n−1}`; ball sum ≍ R² (`sum_ball_min_pow_le`); triangle inequality first, no subset expansion | EK-2+3: 500+800 / low |
| `EKSumDecayNAL` | NOTHING (`Evolution.lean:445` is the same-sign row bound: old `ThetaDecayShort`, `Im m>0`, C after `g,m`) | `KernelExpand.lean:507 ugenCase1Explicit`; `XiBounds.lean:509 xiRowBoundShort` | row `O(1)` from `Prop5Short` (proved) | in EK-3 (~150) / low |
| `EKSumDecay2` | NOTHING (only `latticesum_d3`, `UN_apply_eq_sum_powerset :348`) | none: `Case4.lean:1580 ugenCase4AltExplicit` needs sum-zero AND symmetric (d=2; 3-term expansion `:140`); `XiBounds.lean:598 xiFirstDiff` for `ΔΞ` | new: `S_far/S_near`, BD1 at `ρ ≥ 4`, `(eq:latticesum_d3)`, `log L ≤ W^ε` | EK-4: ~1450 / medium-high |
| `EKSumDecayNonzero` | WEAKER: `Evolution.lean:629 norm_zeroModeSet_UN_le` (`ThetaDecayShort`+`ThetaZeroMode`, `L^{nτ}`, C after `g,m`, `0<(m i).im` ∀i: charge − excluded) | none (d=2 has `Induction/QopBounds.lean:622 qopDecay`, sum-zero `Q_t`) | pins 5s + 8 give a loss-free bound, `Σ_b|Θ̊| ≲ L²/g²` | EK-5: ~450 / low |
### b9 Item 8, split (new files under `RBM3D/Evolution/`; merged `Kernel/*` untouched: b5 shows that besides the root `RBM3D.lean` only `Loop/PureLoop.lean` imports it, and no file outside `Kernel/` names a declaration; PT proofs enter as hypotheses `Prop5Decay`, `Prop6Diff1`, `Prop8ZeroMode`)
| ticket | file | statements | sources | after | role | lines |
|---|---|---|---|---|---|---|
| EK-1 | `Pins.lean` | the pins (`EK*`), `EKsgn`, `EKFastDecay`, `EKSumZero`; bridges `ekSumNdecay_holds`, `ekPropT_holds`, `ekTTk_holds` | this probe | — | prover | 300 |
| EK-2 | `XiPins.lean` | `(eq:decayXi)`, ball sum (pin 5), same-sign row (pin 5s), uniform in g | probe (copy of `SumDecay:376–631`), `Evolution:445–510`; `XiBounds:435–597` | EK-1 | prover-hard | 500 |
| EK-3 | `SumDecay.lean` | `(sum_res_1)`, `(sum_res_2_NAL)`, all n | probe skeleton; `KernelExpand:93–612` | EK-2 | prover-hard | 800 |
| EK-4 | `SumDecayZero.lean` | `ΔΞ` `(eq:Xibb)` (pin 6), `(sumAzero)` ⟹ `(sum_res_2)` | paper A.2 (:159–198); `XiBounds:598–783`, `Case4` template only | EK-2, EK-3 | prover-max | 1450 |
| EK-5 | `Nonzero.lean` | `Σ_b|Θ̊|` (pin 8), `lem:sum_decay_nonzero` loss-free, both charges | `Evolution:520–683` (copy-adapt) | EK-1, EK-2 | prover | 450 |
| EK-6 | `Prec.lean` | pins ⟹ `≺` at `N=(WL)^d` (`W^{Cε} ≤ N^ε`, `Λ=(log W)^{10}`, `log L ≤ W^ε`) | `Bridge.lean` (425 kept) | EK-3..5, ST-D3 | prover | 500 |
6 prover tickets, ≈ 4.0k lines (estimates); with audits and ≤ 3 repairs 12–15 wide count against DECISIONS §9 O2 (25/40/50): under 25, not over 50.
### b10 Item 7, block Anderson reuse (compiled in the probe: `EKuKerQ`, `ek_uKer_eq_uKerQ`, `ek_norm_uKerQ_le`, `ek_sumNdecayQ`, `ek_UN_eq_tensorKerQ`)
Carries over verbatim: `tensorKer`, `zeroModeSet_tensorKer`, `norm_tensorKer_le`, `projMat` (`Evolution.lean:185–426`); `lem:sum_Ndecay` for any `Q_i` with `‖Q_i‖_{∞→∞} ≤ 1` (`ek_sumNdecayQ`; BA: Ward `(eq:WardM)`); `latticesum_d3`, `propT`, `claim:TTk` (functions of `B`, `ℓ`). Generalize: `uKer`/`UN` (built on `μ • SB`) to `EKuKerQ` families; the `Ξ` bounds use `Prop5DecayQ` (T2003 item 6) plus decay of the entries of `Q` (`Mbound_AO`) instead of the nearest-neighbour support of `SB`; `projMat` commutes with `Q` by translation invariance. BA adds: the five PT pins for `M^{(B)}` (constants depending on `λ⁻¹`, `lem_propTH` property 5), `Mbound_AO(2)`, `(eq:WardM)`, `(eq:off_diagM)`.
### b11 Narrative
N1. The seven pins (b2): constants after `(d,n,Λ,κ)`, before `L,g,W,ε,D,s,t,m,σ,A`; `g ∈ (0,Λ]`; both charges (`EKsgn m σ`); no `L^τ`; the PT pins `Prop5Decay`, `Prop5Short` (proved: `prop5Short_holds`), `Prop6Diff1` at `c=1/2`, `Prop8ZeroMode` are antecedents; `Prop7Diff2` is not needed by EK. `(deccA0)` = `EKFastDecay`, `(sumAzero)` = `EKSumZero`.
N2. The merged statements are not strong enough for Steps 3–5 (b5a): all six statements with an old Prop have the constants after `g` (`g,m < C < L,s,t`), two carry `L^τ`, and `norm_zeroModeSet_UN_le` (`Evolution.lean:629`) excludes the charge `−`; EK-2, EK-3 and EK-5 supersede them (nothing outside `Kernel/` names them, b5), so they are retired there.
N3. Three pins are proved by merged theorems (b8, compiled), `(eq:latticesum_d3)` is merged; `(sum_res_1)` at n=2 is derived from `Prop5Decay` (`ekSumDecay1_two`, probe 572–760): triangle inequality first, window/tail split at `R=W^ε ℓ_s`, window sums `1+C_bρ²r`, `(1−s)/(1−t) ≤ 2(ℓ_t²/ℓ_s²)r` (`ek_ratio_le`), constants absorbed with `W^ε ≥ 4`; the two ingredient lemmas are the merged proofs with the witnesses of the decay bound exposed (b4: 4 and 2 removed lines).
N4. Lead checked against the paper: RBM2D `Case3` is the random `sum_res_3` (via `clt-lemma`) and `Case5` the `2k`-kernel; `lem:sum_decay` of 2507.20274 (3_5:1632–1664) has only `(sum_res_1)`, (I), (II): they are not sources. `Case4` needs sum-zero and symmetric tensors; (II) is proved by BD1 (A.2).
N5. Pin hypotheses: none covers `1−t < g²/L² < 1−s` (`lem:sum_decay` needs `t ≤ 1−g²/L²`, `lem:sum_decay_nonzero` needs `s ≥ 1−g²/L²`), as in the paper; the zero-mode term of `B` is dominated by the decay term for `1−t ≥ g²/L²` (`zeroMode_le_of_ge_mul`, `PropT.lean:89`).
N6. Instances (b3) apply each pin at the data shown with every deterministic hypothesis discharged; the far premise of `(deccA0)` is non-vacuous there (`ek_far_point_exists`: a point pair at `ℓ¹` distance 5 ≥ `W^ε ℓ_s` = 5); `Prop5Decay`, `Prop6Diff1`, `Prop8ZeroMode` and the pins `EKSumDecayNAL`, `EKSumDecay2`, `EKSumDecayNonzero` stay hypotheses of their examples. `lem:sum_decay_nonzero` has no admissible `s` at `t=9/10` (needs `s ≥ .99`), hence its window.
N7. Section (a): its row-21 citations are confirmed (b8: 19/19 line ranges); `../RBM2D` HEAD is `9e0f275`, 9 commits past `c9a24cf`, `Evolution/` diff 24 files +713 −3584 (git, read-only; the table of b5 is at `c9a24cf`). No correction to (a), hence no (a′).
## (c) Mathlib names (script `names.py`: `#check` in the probe's import context; deprecated in this Mathlib: `if_pos`, `if_neg`, `if_true`, `if_false`, `push_neg` — probe uses `↓reduceIte`, `not_or`)
Sat Oct  3 03:57:31 UTC 2026
$ python3 names.py
present (34): finTwoArrowEquiv piFinTwoEquiv Fintype.sum_prod_type' Fintype.sum_equiv Finset.sum_filter Finset.sum_mul_sum Finset.sum_ite_eq' Fin.prod_univ_two Fin.forall_fin_two pow_unbounded_of_one_lt Real.rpow_natCast Real.rpow_mul Real.rpow_add Real.rpow_le_rpow_of_exponent_le Real.rpow_two Real.rpow_pos_of_pos Real.rpow_nonneg inv_le_of_inv_le₀ inv_div pi_norm_le_iff_of_nonneg norm_le_pi_norm NormedRing.inverse_one_sub geom_series_mul_neg mul_neg_geom_series hasSum_geometric_of_lt_one tsum_of_norm_bounded norm_pow_le Real.log_le_sub_one_of_pos Real.sqrt_eq_rpow Real.sqrt_sq le_of_sq_le_sq Finset.prod_le_prod₀ Complex.norm_I Complex.I_im
absent (3): Equiv.piFinTwo NormedRing.summable_geometric_of_norm_lt_one NormedRing.tsum_geometric_of_norm_lt_one
## (d) Open issues and paper-delta candidates
- T2016a (necessary at d=3): `(sum_res_2)` carries `log L ≤ W^ε` (paper: "we absorbed it using log L ≤ W^ε", A.2); pin `EKSumDecay2`. T2016b (necessary): `4 ≤ W^ε` in `(sum_res_1)`, `(sum_res_2_NAL)`, `(sum_res_2)`: BD1 is used at `|r| ≤ c|a|`, `c=1/2` ((a) row 15), and the constants of `≲` are absorbed into `W^{C_nε}` only if `W^ε` is bounded below (b7: false at `W^ε ↓ 1`).
- T2016c: `lem:propT` pin = paper, regimes (i),(ii) only; mixed `1−t < g²/L² < 1−u` not covered, no downstream use found. T2016d: `claim:TTk`: `D` is any set with `|a−α| ≤ ℓ` (paper `D_{≤ℓ}`), `ℓ ≥ 1` (D15), `≺` explicit with `Λ²` (`Λ=(log W)^{10}`), `η_t ≍ 1−t` (`(eta)`).
- T2016e (stronger): `lem:sum_decay_nonzero` loss-free, `C‖𝒜‖` with `C(d,n,Λ,κ)`, both charges. T2016f (Lean form): constants uniform in `g ∈ (0,Λ]`, `Λ = 𝔡⁻¹` (T2003a); `(deccA0)`, `(sumAzero)` in the `ℓ¹` distance (D18: a consumer with an `L^∞` window takes `W^ε ↦ d·W^ε`); `(sumAzero)` at the index of value 0.
- Registry (DECISIONS §16): `Prop5Decay`, `Prop8ZeroMode` are borrowed and registered (T2007); `Prop6Diff1` is not yet in `borrowedProps`, class **borrowed** (cited, route H proves it): EK-4, the first ticket that assumes it, lists `RBM3D/Test/Axioms.lean`; `Prop5Short` is proved; `Prop7Diff2` unused. The pins `EKSumDecay1`, `EKSumDecayNAL`, `EKSumDecay2`, `EKSumDecayNonzero`, in the ticket that first lets a consumer (ST-D3) assume them before EK-3..5 merge: **owed** (A.2 proves them; that ticket lists `Axioms.lean`). No Prop is left that no ticket will prove.
- Risk and limits: EK-4 is the one high-risk ticket (new d ≥ 3 argument, numerics only for n=2, (a) rows 13–15); compiled proofs cover three pins, `(sum_res_1)` at n=2 and `ek_sumNdecayQ`, not general n, NAL, `(sumAzero)`, or `lem:sum_decay_nonzero`. EK-6 waits for ST-D3's pin of the `≺` consumer form (RBM2D `Evolution/Defs.lean` `SumDecayDetPrec`, `Bridge.lean`; scale `N=(WL)^d`, DECISIONS §12). Mathlib names to `docs/mathlib-api.md`: the (c) lists.
- Result: items 1–9 delivered (inventory b5; boundary b6; pins b2; exponent table = section (a)(i) with b7; routes b8; skeleton b3; BA b10; split b9; instances b3); probe builds warning-free, every `#print axioms` line is standard (b1); commits on `t/T2016`.
