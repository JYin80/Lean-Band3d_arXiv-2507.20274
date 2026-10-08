Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 13:35:04 UTC 2026

Scripts (Python, no Lean) are in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2336/`: `orders.py`, `numerics.py`, `unif.py`, `symb.py`, `integrals.py`, `instance.py`.
Notation: `s = τ/g²`, `G = 1 - K̂`, `θ_k = 2πk/L` (`zdistD` = ℓ¹ distance, `Defs/Lattice.lean:71`), `M = ⌊d/2⌋+1`, `r = 2M`.

### (i) Exponent table

| item | value | constraint | slack |
|---|---|---|---|
| `Δ_j f(k) = f(k+e_j) - f(k)` on dual torus; `K̂(k) = Σ_a K_{0a} cos(θ_k·a)` | real, even | `Δ_j^r cos(θ·a) = Re[e^{iθ·a}(e^{2πi a_j/L}-1)^r]`; the `a=0` term is constant, so killed for `r ≥ 1` | exact |
| `M` | `⌊d/2⌋+1` | `M > d/2` (second differences), hence `M > (d-1)/2` | `M - d/2 = 1` (d even), `1/2` (d odd) |
| SBP order `r = 2M` | `d+2` (d even), `d+1` (d odd) | `d+1 ≤ 2M ≤ d+2` | `d+2-2M ∈ {0,1}`; `2M-(d+1) ∈ {1,0}` |
| direction `j` | `argmax_j |a_j|_L`, `|a_j|_L ≥ |a|/d` (ℓ¹ norm) | needs `a_j ≠ 0`; in the SBP case `|a|² > τ ≥ 1` | – |
| SBP gain | `|e^{2πi a_j/L}-1|^{-r} ≤ (L/(4|a_j|_L))^r` | `|a_j|_L ≥ 1` | – |
| symbol, `r=1` | `|Δ_j K̂| ≤ C g² L^{-1}(|θ_k|+L^{-1})` | `cos(φ)-1` term `≤ g²L^{-2}`; sine term `|sin(θ·a)||sin φ| ≲ |θ||a||a_j|/L`; moments `Σ K_{0a}|a|^p ≤ C_p g²` by `BAK_off_le` | exact form |
| symbol, `2 ≤ r ≤ 2M` | `|Δ_j^r K̂| ≤ C_r g² L^{-r}` | `≤ (2π/L)^r Σ_{a≠0} K_{0a}|a_j|^r`, `K_{0a} ≤ A g² e^{-2c|a|}` (`KKernel.lean:198`) | `r ≤ d+2` suffices; no bound on `r` is needed for summability (exponential decay) |
| gap | `1-K̂ ≥ c g²|θ|²` (`BAK_gap`, `KSymbol.lean:642`) | `c` depends on `d,Λ,κ` | gives `e^{-cτ|θ|²}` at every `k`, including shifted `k+le_j` |
| `τ ≤ L²` | hypothesis | used for `L^{-1} ≤ τ^{-1/2}`, so `(|θ|+L^{-1}) ≲ τ^{-1/2}` after the Gaussian sum | tight at `τ = L²` |
| Gaussian sum | `L^{-d}Σ_k e^{-cτ|θ_k|²}(|θ_k|+L^{-1})^p ≲ τ^{-(d+p)/2}`, `τ≥1` | product over coordinates `(τ^{-1/2}+L^{-1})^d` | – |
| result `τ ≥ 1`, first diff | `τ^{-(d+1)/2} (τ/|a|²)^M` | all terms exponent `≤ M-(d+1)/2` (table (ii)) | 0 (all-first-difference term is sharp) |
| result `τ ≥ 1`, second diff | `τ^{-(d+2)/2} (τ/|a|²)^M` | exponent `≤ M-(d+2)/2` | 0 |
| `|a|² ≤ τ` (no SBP) | `|diff| ≲ τ^{-(d+q)/2}` from `|e^{iθ_i}-1| ≤ |θ_i|` + Gaussian sum; `(1+|a|²/τ)^{-M} ≥ 2^{-M}` | – | – |
| `τ < 1`, `a ≠ 0` | `kBA τ b ≤ (e^{ASτ}-1)e^{-μ|b|} ≤ C τ e^{-μ|b|}`, `b ≠ 0` | `K = |m|²I + K'`, `P_s = e^{-s(1-|m|²)}Σ s^nK'^n/n!`, `e^{-s(1-|m|²)} ≤ 1`, `Σ_b K'_{ab}e^{μ|a-b|} ≤ A g² S` (`BAK_exp_moment_le`, diagonal `|m|²` cancels), `e^{μ|b|} ≤ ∏e^{μ|x_i-x_{i-1}|}`, `s g² = τ ≤ 1` | `μ = BAct_rate`; uniform in `g ≤ Λ` |
| `τ < 1`, decay | `Cτe^{-μ(|a|-2)} ≤ C'(1+|a|²)^{-M}` | `a`, `a+e_i`, `a+e_j`, `a+e_i+e_j` shift `|·|` by ≤ 2; trivial bound `|diff| ≤ 1` for `|a| ≤ 2` (`0 ≤ kBA ≤ 1`) | – |
| `min(1,τ^{-(d+q)/2})` | `=1` for `τ ≤ 1` | `|diff| ≤ 1` | – |
| P6 integrals (pinned form) | `∫_0^∞ min(1,τ^{-(d+1)/2})(1+|a|²/max(τ,1))^{-M}dτ ≲ |a|^{-(d-1)}`; second `≲ |a|^{-d}` | `τ∈(1,|a|²)`: exponent `M-(d+1)/2 > -1`, resp. `M-(d+2)/2 > -1`; `τ<1`: `|a|^{-2M} ≤ |a|^{-d}` as `2M ≥ d+1` | `M-(d+2)/2+1 = 1` (d even), `1/2` (d odd) |
| Λ, κ dependence | `C = C(d,Λ,κ)` through `A, c, S, μ` | – | numerics: ratio grows with `g` (`g=3`: ~1.4e3), L-bounded |

### (ii) Order of summation by parts versus `d+2` (O2), and the instance

Counting rule (`orders.py`, `τ ≥ 1`, `τ ≤ L²`): after `r=2M` SBP steps, `∇_j^r(F)`, `F = (e^{iθ_i}-1)e^{-sG}`, is expanded: `p` differences on the prefactor (factor `L^{-p}`), `n1` factors `sΔG` (`τL^{-1}(|θ|+L^{-1})`), `n2` factors `sΔ^{r_i}G`, `r_i ≥ 2` (`τL^{-r_i}`); powers of `L` cancel against `L^r`; each `|θ|, L^{-1}` counts `τ^{-1/2}`. Factors of `e^{-sΔG}-1` are controlled by `|sΔG| ≲ τ L^{-1}(|θ|+L^{-1})` and `cτ|θ|² ≥ cτ(2π/L)²` for `k ≠ 0`, so `e^{|sΔG|}e^{-cτ|θ|²} ≤ e^{-cτ|θ|²/2}` for `|θ| ≥ C'/L`, and `|sΔG| ≲ τ/L² ≤ 1` below that.
```
$ python3 orders.py
d  M=floor(d/2)+1  2M  d+2  2M<=d+2  2M>=d+1 | worst tau-exp (q=1)  target  slack | (q=2) worst target slack | max symbol diff order used
2  2  4  4  True  True | 1/2  1/2  0 (p,n1,n2)=(0, 4, 0) | 0  0  0 (p,n1,n2)=(0, 4, 0) | 4
3  2  4  5  True  True | 0  0  0 (p,n1,n2)=(0, 4, 0) | -1/2  -1/2  0 (p,n1,n2)=(0, 4, 0) | 4
4  3  6  6  True  True | 1/2  1/2  0 (p,n1,n2)=(0, 6, 0) | 0  0  0 (p,n1,n2)=(0, 6, 0) | 6
5  3  6  7  True  True | 0  0  0 (p,n1,n2)=(0, 6, 0) | -1/2  -1/2  0 (p,n1,n2)=(0, 6, 0) | 6
6  4  8  8  True  True | 1/2  1/2  0 (p,n1,n2)=(0, 8, 0) | 0  0  0 (p,n1,n2)=(0, 8, 0) | 8
```
Reading: `2M ≤ d+2` for every `d` (equality for even `d`), highest symbol difference used `= 2M` (the single factor `Δ_j^{2M}K̂`, bound `g²L^{-2M}`); every term is a finite torus sum (no summability issue; the moments `Σ K_{0a}|a_j|^{2M}` are finite by exponential decay). The extremal term is `n1 = r` (all first differences), slack 0: the exponent closes exactly, so each `sΔG` must keep its `(|θ|+L^{-1})` factor; the cruder `|Δ_jK̂| ≲ g²L^{-1}` would lose `τ^{n1/2}` and FAIL.

Instance (Lean flow point `P`, `MFixedPoint.lean:893`, reproduced numerically: `w=6i/5`, `L=4`, `g=10`, `d=3`):
```
$ python3 instance.py
mS=-0.000000+0.261969j zS=0.000000+0.938031j t0=0.218307 | g0=4.672337 (0<g0<=10) E=0.000000 m0=-0.000000+0.560680j kappa=Im m0=0.560680
BASelf(3,4,g0,E,m0) residual |m0 - L^-3 tr(...)| = 1.11e-16;  Im m0 > 0: True;  kappa <= Im m0: True (equality)
row sum K = 1.000000000000, K_00=|m0|^2=0.314363, K[1,0,0]=5.981613e-04
tau=1: kBA(0)=0.969182, kBA(e_0)=0.000027; worst ratio D1 18.6935, D2 24.2423 over all a in Z_4^3, i, j
all hypotheses: d=3>=2, L=4>=3, 0<g0=4.6723<=Lambda=10, BAReal holds (residual above), 0<tau=1<=16
```
Hypotheses of both targets hold at once (`d=3`, `Λ=10`, `κ=Im m0`, `L=4`, `g=g0`, `τ=1`, all `a, i, j`); no `N=0`, empty index, or collapsed window. Hypothesis `BAReal` is not external (it is a deterministic predicate; the point exists by `exists_flowPt`).

### (iii) The `max τ 1` correction (`numerics.py`, d=3, E=0.1, numerically solved `BASelf`, `τ ∈ [1e-3, L²]` 60-point log grid, all `a ∈ Z_L^3`, all `j` (and `i,j`))
```
$ python3 numerics.py | awk (3 of 6 configurations shown)
L=8 g=0.3 E=0.1: m = -0.034939 + 0.822989 i, BASelf residual 1.16e-16, row sum K = 1.000000000000, K_00 = |m|^2 = 0.678532 (0.678532)
   worst ratio |D1|/[min(1,tau^-(d+1)/2)(1+|a|^2/max(tau,1))^-M] = 3.9843 at (tau,j)=0.001,0
   worst ratio |D2|/[min(1,tau^-(d+2)/2)(1+|a|^2/max(tau,1))^-M] = 24.8948 at (tau,i,j)=0.001,1,0
   NEGATIVE CONTROL (1+|a|^2/tau)^-M: worst D1 ratio = 9.981e+05 (at tau=0.001), worst D2 ratio = 1.594e+07
   tau=0.001: |kBA(a+e_0)-kBA(a)| at a=(2,0,0) = 1.268e-05, /tau = 0.0127; (1+|a|^2/tau)^-M = 6.247e-08
L=12 g=1.0 E=0.1: m = -0.021213 + 0.432469 i, BASelf residual 2.78e-16, row sum K = 1.000000000000, K_00 = |m|^2 = 0.187479 (0.187479)
   worst ratio |D1|/[min(1,tau^-(d+1)/2)(1+|a|^2/max(tau,1))^-M] = 337.6280 at (tau,j)=1.148,2
   worst ratio |D2|/[min(1,tau^-(d+2)/2)(1+|a|^2/max(tau,1))^-M] = 661.3940 at (tau,i,j)=1.718,2,2
   NEGATIVE CONTROL (1+|a|^2/tau)^-M: worst D1 ratio = 1.001e+06 (at tau=0.001), worst D2 ratio = 1.599e+07
L=12 g=3.0 E=0.1: m = -0.043576 + 0.298826 i, BASelf residual 2.37e-16, row sum K = 1.000000000000, K_00 = |m|^2 = 0.091196 (0.091196)
   worst ratio |D1|/[min(1,tau^-(d+1)/2)(1+|a|^2/max(tau,1))^-M] = 1366.5992 at (tau,j)=10.51,0
   worst ratio |D2|/[min(1,tau^-(d+2)/2)(1+|a|^2/max(tau,1))^-M] = 8089.9075 at (tau,i,j)=15.73,0,0
   NEGATIVE CONTROL (1+|a|^2/tau)^-M: worst D1 ratio = 1.002e+06 (at tau=0.001), worst D2 ratio = 1.601e+07
```
The `max τ 1` form holds with bounded ratios; at fixed `a=(2,0,0)` the difference is `≍ τ` (`/τ` constant), so the literal `(1+|a|²/τ)^{-M}` fails (ratio `~1e6` at `τ=1e-3`, growing like `τ^{-1}`).
L-uniformity (`unif.py`, `τ ∈ [1, L²]`, `g=0.3`; worst ratios D1/D2): `L=8: 2.24/3.21; 12: 2.51/4.57; 16: 2.59/5.17; 24: 2.71/5.63; 32: 2.69/5.79` (saturating). `g=1`: `385/690, 338/663, 325/667, 168/361, 67/149` for `L=8,12,16,24,32` (decreasing; the kernel's correlation length is long, constant depends on `Λ, κ`).
Symbol regularity (`symb.py`, `g=0.3`, sup over `k, j` of `|Δ_j^rK̂|/bound_r`): `L=8: 42.41, 84.81, 479.87, 5603.49, 36530.10`; `L=16: 46.23, 92.47, 593.34, 7827.60, 78803.43`; `L=32: 47.29, 94.57, 636.95, 8629.55, 91685.15` for `r=1..5` (`r=1` bound `g²L^{-1}(|θ_k|+L^{-1})`, `r≥2` bound `g²L^{-r}`); saturating (cap `(2π)^r g^{-2}Σ_aK_{0a}|a_j|^r`, moments `1.086` for `r=5`).
P6 integral check (`integrals.py`, `I1·|a|^{d-1}`, `I2·|a|^d`, `|a| = 1..1e5`, upper cutoff `∞`):
```
d M | max over |a| in {1,10,1e2,1e3,1e4,1e5} of I1*|a|^(d-1) and I2*|a|^d  | control M-1
2 2 | I1: 1.54 1.57 1.57 1.57 1.57 1.57 | I2: 0.75 1 1 1 1 1 | ctrl I1: 2.07 3.04 3.13 3.14 3.14 3.14 | ctrl I2: 1.19 5.61 10.2 14.8 19.4 24
3 2 | I1: 0.75 1 1 1 1 1 | I2: 0.535 1.47 1.56 1.57 1.57 1.57 | ctrl I1: 1.19 5.61 10.2 14.8 19.4 24 | ctrl I2: 0.929 27 297 3e+03 3e+04 3e+05
4 3 | I1: 0.321 0.393 0.393 0.393 0.393 0.393 | I2: 0.25 0.5 0.5 0.5 0.5 0.5 | ctrl I1: 0.535 1.47 1.56 1.57 1.57 1.57 | ctrl I2: 0.443 4.61 9.21 13.8 18.4 23
5 3 | I1: 0.25 0.5 0.5 0.5 0.5 0.5 | I2: 0.214 1.08 1.17 1.18 1.18 1.18 | ctrl I1: 0.443 4.61 9.21 13.8 18.4 23 | ctrl I2: 0.394 25.5 295 3e+03 3e+04 3e+05
6 4 | I1: 0.119 0.197 0.196 0.196 0.196 0.196 | I2: 0.104 0.333 0.333 0.333 0.333 0.333 | ctrl I1: 0.214 1.08 1.17 1.18 1.18 1.18 | ctrl I2: 0.193 4.11 8.71 13.3 17.9 22.5
```
So the pinned form integrates to `|a|^{-(d-1)}` (first) and `|a|^{-d}` (second) with `M=⌊d/2⌋+1`, and `M-1` fails (`d=2` second, `d=3` first/second, ...). The `max τ 1` form is sufficient for P6's integrals `∫e^{-(1-t)u}(…)du` (weight `≤ 1` only helps).

### (iv) §29 and verdict
- §29 (1) time domain: `s = τ/g² > 0` since `τ > 0`, `g > 0`; no `t` appears. (2) regime boundary: `τ ≤ L²` is a hypothesis (used for `L^{-1} ≤ τ^{-1/2}`); `kBA_gap` (regime (ii)) covers `τ ≥ L²`, the closed ranges meet at `τ = L²`; no `ilambda`. (3) no `W`, no `L`-vs-`W` relation; `L ≥ 3` only. (4) no `n`: `∀ L ≥ 3`, `∀ g ∈ (0,Λ]`, constant `C(d,Λ,κ)` independent of `L, g, E, m, τ, a, i, j`; nothing eventual. External input: none (`BAK_off_le`, `BAK_exp_moment_le`, `BAK_gap`, `kBA_fourier`, `BAKhat_eq` are merged Lean).
- Open point for 1b (not a failure): the Faà di Bruno step for `Δ_j^r e^{-sG}` needs the `e^{|sΔG|}e^{-cτ|θ|²}` absorption shown above, and slack 0 means no `τ` can be lost anywhere.

**Verdicts:** `kBA_diff1_le` PASS; `kBA_diff2_le` PASS; `BAKhat_diff_le` (shape: `|Δ_jK̂| ≤ C g²L^{-1}(|θ_k|+L^{-1})`, `|Δ_j^rK̂| ≤ C_r g²L^{-r}` for `2 ≤ r ≤ d+2`, uniform in `L ≥ 3`, `g ∈ (0,Λ]`) PASS.

## (b) Script output (prover stage; `date -u` stamps inside the blocks)

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2336`, branch `t/T2336`; sole file `RBM3D/BA/KHeatDiff.lean` (new).
```
$ date -u
Thu Oct  8 14:46:04 UTC 2026
$ git log --oneline main..t/T2336 | cat
462ebdd T2336: instances at the ticket data (tau = 1)
8fd6f2d T2336: KHeatDiff sections 10-11 (public symbol regularity, instances), docstring, compaction
0e0f6c0 T2336: KHeatDiff sections 8-9 (regime tau <= 1, the two target theorems)
ec301a3 T2336: KHeatDiff sections 6-7 (SBP, Gaussian sum, Fourier bound, regime 1 <= tau <= L^2)
0517b91 T2336: KHeatDiff section 5 (per-frequency bound for Delta_j^R of the Fourier summand)
96cc9c2 T2336: KHeatDiff sections 1-4 (difference calculus, characters, moments, symbol, sequence lemmas)
$ git diff --stat main...t/T2336
 RBM3D/BA/KHeatDiff.lean | 1757 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1757 insertions(+)
$ wc -l RBM3D/BA/KHeatDiff.lean
    1757 RBM3D/BA/KHeatDiff.lean
$ grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/BA/KHeatDiff.lean
0
$ grep -n '^import' RBM3D/BA/KHeatDiff.lean
6:import RBM3D.BA.KHeatTail
7:import Mathlib.Algebra.Group.ForwardDiff
$ grep -rn 'kBA_diff1_le\|kBA_diff2_le\|BAKhat_diff_le\|KHeatDiffInst\|KHeatDiff_' RBM3D/ --include='*.lean' | grep -v 'RBM3D/BA/KHeatDiff.lean' | grep -v 'RBM3D/Probe/' | wc -l
       0
$ public declarations:
1573:theorem kBA_diff1_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < 
1599:theorem kBA_diff2_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < 
1656:theorem BAKhat_diff_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 
1722:theorem inst_diff1 :
1731:theorem inst_diff2 :
1742:theorem inst_symb :
$ ports (sources of the copied private lemmas, last commit touching each file on main):
RBM3D/BA/KHeat.lean 8a6c908
RBM3D/BA/KHeatTail.lean d002ba6
RBM3D/BA/KSymbol.lean 0da5856
$ grep -n 'RBM1D\|RBM2D' RBM3D/BA/KHeatDiff.lean   (nothing is ported from the sister projects, so no `git -C ../RBM{1,2}D diff --stat`)
23:Ports of private lemmas of merged RBM3D files (nothing from `../RBM1D`, `../RBM2D`): `KHeat.lean` `KHeat_chi` `:180`,
```
```
$ date -u
Thu Oct  8 14:46:12 UTC 2026
$ lake build RBM3D.BA.KHeatDiff 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3744 jobs).
$ lake env lean axioms.lean   (#print axioms of the 3 theorems and 3 instances)
'RBM.BA.kBA_diff1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_diff2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKhat_diff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatDiffInst.inst_diff1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatDiffInst.inst_diff2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatDiffInst.inst_symb' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.BA.KHeatDiff; #assert_rbm_axioms)
exit code: 0
axiom audit: 10111 theorems, 3011 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
lines of the output mentioning KHeatDiff: 0
$ lake env lean checkeq.lean   (check-file imports + import RBM3D.BA.KHeatDiff + example : RBM.BA.T2336Check.T2336_kBA_diff{1,2}_le := RBM.BA.kBA_diff{1,2}_le)
exit code: 0; error lines: 0
$ lake build   (whole library in the worktree)
Build completed successfully (4144 jobs).
$ date -u
Thu Oct  8 14:47:07 UTC 2026
```
Target statements, extracted by script:
```
Thu Oct  8 14:48:49 UTC 2026
$ python3 stmtdiff.py   (bodies of the two targets vs docs/tickets/checks/T2336-check.lean)
kBA_diff1_le statement bodies identical after whitespace normalization: True ( 378 chars )
kBA_diff2_le statement bodies identical after whitespace normalization: True ( 472 chars )
$ sed -n "/^theorem kBA_diff1_le/,/:= by/p; ..." RBM3D/BA/KHeatDiff.lean   (the three public targets)
theorem kBA_diff1_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (j : Fin d),
        |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
          ≤ C * min 1 (τ ^ (-((d : ℝ) + 1) / 2))
            * (1 + (zdistD d L a : ℝ) ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ))) := by
theorem kBA_diff2_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (i j : Fin d),
        |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
            - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
          ≤ C * min 1 (τ ^ (-((d : ℝ) + 2) / 2))
            * (1 + (zdistD d L a : ℝ) ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ))) := by
theorem BAKhat_diff_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ (j : Fin d) (k : Zd d L),
        |fwdDiff (Pi.single j (1 : ZMod L)) (BAKhat d L g E m) k|
            ≤ C * g ^ 2 * (L : ℝ)⁻¹ * (Real.sqrt (BAthetaSq d L k) + (L : ℝ)⁻¹) ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ N →
          |(fwdDiff (Pi.single j (1 : ZMod L)))^[i] (BAKhat d L g E m) k| ≤ C * g ^ 2 * ((L : ℝ)⁻¹) ^ i := by
```
Compiled nonempty instances (extracted by `sed`, blank lines and docstrings removed; `d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, flow point `P` of `MFixedPointInst`; every deterministic hypothesis is discharged by `P.real`, `P.g0_pos`, `P.g0_le`; `τ = 1 ≤ L² = 16`, `a = (1,0,2)`, `|a| = 3`; the ticket's instance data):
```
namespace KHeatDiffInst
open RBM.BA.MFixedPointInst
theorem inst_diff1 :
    ∃ C : ℝ, 0 < C ∧
      |kBA 3 4 P.g0 P.E P.m0 1 (![1, 0, 2] + Pi.single 0 1) - kBA 3 4 P.g0 P.E P.m0 1 ![1, 0, 2]|
        ≤ C * min 1 ((1 : ℝ) ^ (-(((3 : ℕ) : ℝ) + 1) / 2))
          * (1 + ((zdistD 3 4 ![1, 0, 2] : ℕ) : ℝ) ^ 2 / max (1 : ℝ) 1) ^ (-(((3 / 2 + 1 : ℕ) : ℝ))) := by
  obtain ⟨C, hC, h⟩ := kBA_diff1_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨C, hC, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 one_pos (by norm_num) _ 0⟩
theorem inst_diff2 :
    ∃ C : ℝ, 0 < C ∧
      |kBA 3 4 P.g0 P.E P.m0 1 (![1, 0, 2] + Pi.single 0 1 + Pi.single 2 1)
          - kBA 3 4 P.g0 P.E P.m0 1 (![1, 0, 2] + Pi.single 0 1)
          - kBA 3 4 P.g0 P.E P.m0 1 (![1, 0, 2] + Pi.single 2 1) + kBA 3 4 P.g0 P.E P.m0 1 ![1, 0, 2]|
        ≤ C * min 1 ((1 : ℝ) ^ (-(((3 : ℕ) : ℝ) + 2) / 2))
          * (1 + ((zdistD 3 4 ![1, 0, 2] : ℕ) : ℝ) ^ 2 / max (1 : ℝ) 1) ^ (-(((3 / 2 + 1 : ℕ) : ℝ))) := by
  obtain ⟨C, hC, h⟩ := kBA_diff2_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨C, hC, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 one_pos (by norm_num) _ 0 2⟩
theorem inst_symb :
    ∃ C : ℝ, 0 < C ∧
      |fwdDiff (Pi.single (1 : Fin 3) (1 : ZMod 4)) (BAKhat 3 4 P.g0 P.E P.m0) ![1, 0, 2]|
          ≤ C * P.g0 ^ 2 * ((4 : ℕ) : ℝ)⁻¹ * (Real.sqrt (BAthetaSq 3 4 ![1, 0, 2]) + ((4 : ℕ) : ℝ)⁻¹) ∧
      |(fwdDiff (Pi.single (1 : Fin 3) (1 : ZMod 4)))^[3] (BAKhat 3 4 P.g0 P.E P.m0) ![1, 0, 2]|
          ≤ C * P.g0 ^ 2 * (((4 : ℕ) : ℝ)⁻¹) ^ 3 := by
  obtain ⟨C, hC, h⟩ := BAKhat_diff_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1 5
  obtain ⟨h1, h2⟩ := h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 ![1, 0, 2]
  exact ⟨C, hC, h1, h2 3 (by norm_num) (by norm_num)⟩
end KHeatDiffInst
```
Narrative (facts; the file's own header docstring has the same route):
- Delivered: `kBA_diff1_le`, `kBA_diff2_le` (bodies equal to the check file after whitespace normalization; the two `example`s elaborate) and the public `BAKhat_diff_le`; 1757 lines (stop line 1800).
- §1 geometric calculus on `ℕ → ℂ`: `KHeatDiff_Geo R B ρ φ := ∀ i ≤ R, ∀ l, l + i ≤ R → ‖Δ^i φ l‖ ≤ B ρ^i` is stable under products (induction on the order, no binomial sums), powers and `exp` (`‖Δ^i e^φ‖ ≤ i! ρ^i e^{eB}` by `n^i ≤ i! e^n`). It replaces a Faà di Bruno formula; `ForwardDiff.lean` has no product rule for `fwdDiff` (names `fwdDiff_mul`, `fwdDiff_iter_mul` absent, list (c)).
- §2-3 characters `χ_k(a)`; all moments `Σ_a K_{0a}|a|^q ≤ C g²`; `Δ_j^i K̂(k) = Σ_a K_{0a} χ_k(a)(χ_{e_j}(a) − 1)^i` (`BAKhat_eq`) gives `|Δ_j^i K̂| ≤ (2π/L)^i Σ_a K_{0a}|a|^i`; the first difference keeps its factor `ϑ = |θ_k|` through `|Im χ_k(a)| ≤ ϑ|a|`, which the preflight requires (a: "each `sΔG` must keep its `(|θ|+L^{-1})` factor").
- §4-5 `KHeatDiff_perk`: for `1 ≤ τ ≤ L²`, `‖Δ_j^R(A·Π_{u<n}(χ_·(e_{i_u}) − 1))(k)‖ ≤ C (√τ/L)^R (√τ)^{-n} e^{-c₁τ|θ_k|²}`; the line sequences `w` (symbol) and `p` (prefactor) are `Geo` with ratio `K(√τ/L)(1 + ξ)`, `ξ = √τ(|θ_k| + (9R+9)/L)`; the factors `e^{O(ξ)}` and polynomials in `ξ` are absorbed by `BAK_gap` at the base point `k` only.
- §6 summation by parts `Σ_k Δ_j^R F χ_k(a) = (e^{−2πi a_j/L} − 1)^R Σ_k F χ_k(a)` with `|e^{2πi y/L} − 1| ≥ 4|y|_L/L`; Gaussian sum `L^{-d}Σ_k e^{−w|θ_k|²} ≤ C w^{-d/2}` from the merged `Heat.kProd_le`; `KHeatDiff_four` combines them.
- §7 `1 ≤ τ ≤ L²`: `|a|² ≤ τ` uses `R = 0`; `|a|² > τ` uses `R = 2M`, `M = ⌊d/2⌋+1`, in the direction `j₀` of the largest `|a_{j₀}|_L ≥ |a|/d` (`KHeatDiff_A`). §8 `0 < τ ≤ 1`: the merged `kBA_le` gives `kBA τ b ≤ C e^{-c|b|}` (`b ≠ 0`), then `e^{-cr}(1+r²)^M ≤ (2M)!2^M/c^{2M}` (`KHeatDiff_B`). §9 `KHeatDiff_diff1/2` write the differences as real parts of Fourier sums (`kBA_fourier`); `KHeatDiff_comb` assembles both regimes into the pinned shape with `max τ 1`.
- Differences from the ticket and from (a): (i) no bound on the order of summation by parts is used (finite torus sums; every moment of `K` is finite by `BAK_exp_moment_le`), so (a)(ii)'s `2M ≤ d+2` is not needed and the table stays valid; (ii) the regime `τ ≤ 1` uses the merged `kBA_le` (T2335) instead of the power-series route of the ticket, hence the import `RBM3D.BA.KHeatTail`; (iii) constants use `π ≤ 4` (`Real.pi_le_four`).
- No external input; no public `Prop` predicate (`KHeatDiff_Geo` is `private`); registry pre-check exit code 0. Constants depend on `(d, Λ, κ)` only (and on `N` for `BAKhat_diff_le`); `2 ≤ d` as in the check file.

## (c) Verified Mathlib names (`#check @name` for 159 names, extracted from the file plus a hand list, in an environment importing the new module: 0 errors)
- `fwdDiff`, `fwdDiff_const (h) (g)` (`h` explicit), `fwdDiff_iter_eq_sum_shift`, `fwdDiff_iter_add`, `fwdDiff_iter_const_smul`, `fwdDiff_iter_comp_add` (`Mathlib/Algebra/Group/ForwardDiff.lean`); `hasSum_sum`, `HasSum.norm_le_of_bounded`, `HasSum.const_smul`, `HasSum.mul_left`.
- `NormedSpace.expSeries_div_hasSum_exp`, `Complex.exp_eq_exp_ℂ`, `Real.exp_eq_exp_ℝ`, `Real.pow_div_factorial_le_exp (x) (hx : 0 ≤ x) (n)`, `Real.exp_nat_mul`, `Real.add_one_le_exp`.
- `ZMod.stdAddChar_coe`, `ZMod.stdAddChar_apply`, `Circle.norm_coe`, `ZMod.coe_valMinAbs`, `ZMod.valMinAbs_natAbs_eq_min`, `AddChar.map_nsmul_eq_pow`, `Complex.norm_exp_I_mul_ofReal_sub_one`, `Real.norm_exp_I_mul_ofReal_sub_one_le`, `Real.mul_le_sin`, `Real.pi_le_four`, `Real.one_sub_sq_div_two_le_cos`.
- `Real.le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ √y ↔ x ^ 2 ≤ y`, `Real.one_le_sqrt`, `Real.sqrt_le_iff`, `Real.sq_sqrt`, `Real.sqrt_mul`, `Real.sqrt_eq_rpow`, `Real.rpow_neg`, `Real.rpow_natCast`, `Real.one_le_rpow_of_pos_of_le_one_of_nonpos`.
- Verified absent (script: `Unknown constant/identifier` in this import closure): `Real.pi_gt_three`, `Real.pi_lt_d2` (they live in `Mathlib.Analysis.Real.Pi.Bounds`, not imported), `Real.pi_ge_two`, `fwdDiff_mul`, `fwdDiff_iter_mul`.

## (d) Open issues and paper-delta candidates
1. Size 1757 lines: the stop line (1800) is not reached; the last number of the size triple (1700) is exceeded by 57 lines.
2. Imports beyond the ticket's list: `RBM3D.BA.KHeatTail` (`kBA_le`, regime `τ ≤ 1`) and `Mathlib.Algebra.Group.ForwardDiff` (`fwdDiff`).
3. P6 interface: the pinned shape is `C·min 1 τ^{-(d+q)/2}·(1 + |a|²/max τ 1)^{-M}`, `q = 1, 2`; (a)(iii) checks numerically that it integrates to `|a|^{-(d-1)}` resp. `|a|^{-d}`; no Lean statement of that integral here (P6's Laplace lemma).
4. `BAKhat_diff_le` (shape reported for P6's pin): `|Δ_j K̂(k)| ≤ C g² L^{-1}(|θ_k| + L^{-1})` and `|Δ_j^i K̂(k)| ≤ C g² L^{-i}` for `1 ≤ i ≤ N`, `N` arbitrary, uniform in `L ≥ 3`, `g ∈ (0, Λ]`.
5. T2336a (statement difference): the decay factor is `(1 + |a|²/max τ 1)^{-M}` (dispatcher's correction in the ticket; the literal `(1 + |a|²/τ)^{-M}` of supervisor 1048 C4 fails as `τ → 0`: (a)(iii) negative control, ratio `~1e6` at `τ = 1e-3`); and the paper (`A:50-56`) cites summation by parts for `Θ̂` ([yang2024Del]) while Lean proves the bounds for the Fourier summand of the heat kernel `kBA = P_s(0, ·)` (C4).
6. T2336b: `BAKhat_diff_le` is a new statement (one-direction regularity of the symbol of `K = |M^{(B)}|²`, all orders `i ≤ N`, refined first difference); the paper uses it only implicitly (`A:50-56`).
7. T2336c: the regime `τ ≤ 1` is obtained from the merged `kBA_le`, a Lean-only route.
