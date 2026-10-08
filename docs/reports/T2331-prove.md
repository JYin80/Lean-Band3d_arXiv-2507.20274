Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 12:00 UTC 2026

Notation: `K = BAK` (`= M^{(+,-)}`), `θ_k = 2πk/L`, `K̂ = BAKhat`, `|θ_k|² = BAthetaSq`, `P_s = BAP`, `kBA τ = P_{τ/g²}(0,·)`.
Sources: ticket T2331 and `docs/tickets/checks/T2331-check.lean`; `docs/supervisor/2026-10-08-1048.md` C1/C2; paper `A_deterministic_estimates.tex` lines 16-20 (Taylor series `(eq;Taylor)`, `|Θ^{(σ)}| ≤ Θ^{(+,-)}`, row sum `(1-t)^{-1}`; the ticket's "A:22-67" is these lines and 58-66 in the file) and `BA/KSymbol.lean:642` (`BAK_gap`).

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| definitions | `P_s = e^{-s}Σ_n sⁿ/n! Kⁿ`, `kBA τ = P_{τ/g²}(0,·)`, `g>0` | `g² s = τ`; at `τ=0`: `0^0=1`, `P_0 = 1` | exact |
| Laplace: `t`, Gamma integral | `∫₀^∞ e^{-u}(tu)ⁿ/n! du = tⁿ`; `e^{-(1-t)u}·e^{-tu}=e^{-u}` | `0 ≤ t < 1` (Neumann series of `1-tK` needs `‖K‖_{∞→∞}=1` by `BAK_pow_row_sum`, so `t<1` is sharp); `kBA ≤ 1` and `∫ e^{-(1-t)u}du = (1-t)^{-1}` finite | exact identity; at `t=0` both sides `δ_0` |
| time substitution | `kBA(t g² u) = P_{tu}` | `g ≠ 0` (`0<g`) | exact |
| Fourier: `Kⁿ(0,a) = L^{-d}Σ_k K̂(k)ⁿcos(θ_k·a)` | circulant + even (`BAK_shift`, `BAK_zero_neg`, unconditional in `L ≥ 1`, no `BASelf`) | none; `kBA τ a = L^{-d}Σ_k e^{-(τ/g²)(1-K̂)}cos(..)` for all real `τ`, `g>0` | exact |
| symbol gap `c_g` | `c_g = 4c₀/π²`, `c₀ = κ²/(4(4dΛ+3)⁸)` (`BAK_gap`), `1-K̂ ≥ c_g g²|θ_k|²` | `BAReal`, `0<g≤Λ`, `d>0`; used for `τ ≥ 0` only, `1-K̂ ≥ 0` so `e^{-(τ/g²)(1-K̂)} ≤ e^{-c_g τ|θ_k|²}` with no `g` left | `d=3, Λ=10`: `c_g = 9.4e-19` at `κ=0.6988` vs empirical `min(1-K̂)/(g²|θ|²) = 0.068` (below); no laziness (`BAK_lazy`) used |
| diag-bound sum | per coordinate `L^{-1}Σ_{j∈ℤ}e^{-c_g τ(2πj/L)²} ≤ L^{-1} + (4π c_g τ)^{-1/2}` | `τ>0`; product over `d` coordinates (`(x+y)^d ≤ 2^{d-1}(x^d+y^d)`) | `C = 2^{d-1}max(1,(4πc_g)^{-d/2})`, depends on `(d,Λ,κ)` only; for `τ ≤ 1`: `kBA ≤ 1 = min(1,τ^{-d/2})` |
| regime (ii) cut | `τ ≥ L²` (diffusive time, not `s ≥ L²`) | for `k≠0`: `|θ_k|² ≥ (2π/L)²` so `c_g τ|θ_k|² ≥ 4π²c_g τ/L²` | at `τ=L²`: the factor `e^{-c τ/L²}` is `e^{-c}`; no relation between `g`, `L` needed (`g` cancelled above), so `g ∈ (0,Λ]` small is covered |
| gap, value `|kBA-L^{-d}|` | exponent `L^{-d}`; `Σ_{k≠0}e^{-c_gτ|θ_k|²} ≤ e^{-2π²c_gτ/L²}·(Σ_{j∈ℤ}e^{-2π²c_g j²τ/L²})^d`, bracket `≤ 1+(2π c_g)^{-1/2}` for `τ≥L²` | `c = 2π²c_g`; `C ≥ (1+(2πc_g)^{-1/2})^d` | `C` huge (`≈ (4e8)^d` at the Lean `c_g`) but only `∃ C`; concrete instance below uses the true rate |
| gap, 1st difference | exponent `L^{-(d+1)}`: `|e^{iθ_j}-1| ≤ |θ_j|`, `sup_x x e^{-c_gτx²/2} = (e c_g τ)^{-1/2} ≤ L^{-1}(e c_g)^{-1/2}` | `τ ≥ L²` (gives `τ^{-1/2} ≤ L^{-1}`); `k=0` term cancels in a difference | closes with exponent `d+1` exactly, no loss |
| gap, 2nd difference | exponent `L^{-(d+2)}`: `|θ_i||θ_j| ≤ |θ|²`, `sup_x x²e^{-c_gτx²/2} = 2/(e c_g τ) ≤ L^{-2}·2/(e c_g)` | `τ ≥ L²` | closes with exponent `d+2` exactly |
| shift well-defined | `a ↦ a+Pi.single j 1` changes the phase by `θ_{k_j}` mod `2π` (`val` wraps) | cos is `2π`-periodic | exact |
| `cos(φ+θ)-cos φ` | `|·| ≤ 2|sin(θ/2)| ≤ |θ_zdist|`, `θ_zdist = 2π zdist(k_j)/L ≤ π` | `zdist ≤ L/2` | exact |
| `L` | `3 ≤ L` (statements) | only `BAK_gap`/torus sums; no `L`-`g` relation; no `W`; all `L ≥ 3`, no `∀ᶠ` | §29 (1)-(4): see (iii) |
| constants order | `d, Λ, κ` then `∃ C (c)` then `L, g, E, m, τ, a` | as `kProd_gap` (`HeatProduct.lean:626`) | matches |

DECISIONS §29 checks (one line each), for the six targets: (1) time domain: Laplace needs `0 ≤ t < 1` (pinned); `kBA_basic` nonnegativity/mass need `0 ≤ τ` (pinned), evenness/continuity/Fourier hold for all real `τ` (series entire in `s`); `kBA_gap` `τ ≥ L² > 0`, `kBA_diag_le` `τ > 0`; the semigroup is pinned at `s,s' ≥ 0`. (2) the cut `τ ≥ L²` has no `1-ilambda²/L²` boundary and no negative-time reach: it is independent of `g`. (3) no `W`, no `L^d ≤ W^K`: nothing about `L`-`W` is used; constants depend on `(d,Λ,κ)` only. (4) all statements are `∀ L ≥ 3`, none `∀ᶠ`; no finite-`n` condition is forced.
Note on the paper: `(eq;Taylor)` (tex line 16) and the row-sum identity (line 20) are the discrete Neumann series; the Poisson semigroup, the Laplace identity and regime (ii) are not in the paper (it only sketches the random-walk route, lines 58-66); they are the supervisor's C1/C2 design (Lean-side lemmas, proved from `BAK_gap`), paper-delta candidate `T2331a` for the Poisson/diffusive-time form.

### (ii) One concrete nondegenerate instance

`d=3`, `L ∈ {4,6,8}` (`L³ ∈ {64,216,512}` points), BASelf point solved numerically by the fixed point `m = L^{-3}Σ_λ 1/(gλ-E-m)`, `λ` the eigenvalues of the block adjacency `PsiB` (`Adj`: `zdistD = 1`, degree 6), `K = |(gΨ-(E+m))^{-1}|²` entrywise (`BAMB`, `BAK`), `Λ=10`, `κ = Im m` (so `BAReal`: `0<g≤Λ`, `κ ≤ Im m`). `kBA` computed by the Fourier form and by the Poisson power series (`τ/g²` terms up to `s+60√s+60`); gap ratios are sup of lhs/rhs over sampled `a`, all `i,j`, with `c' = 0.95·L²·min_{k≠0}(1-K̂)/g²` (the true rate), at `τ = L², 2L², 4L²`: finite `C`. Also checked: `τ=0` is `δ_0`, `Σ_a kBA 1 = 1`, nonneg, `kBA ≤ 1`, semigroup (`s=0.7`, `s'=1.3`), Laplace identity at `t=0.7` against `(1-tK)^{-1}(0,a)` by quadrature, `kBA_diag_le` constant on a `τ`-grid `{0.05,…,3L²}`, and `Lean c_g ≤` empirical gap ratio. The Lean instance (`KHeatInst`) uses the existing flow point `P` (`g0 ≤ 10`, `BAReal 3 4 g0 (Im m0) E m0`); `P` is an existential choice, so the numeric point is a stand-in with the same hypotheses.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2331/final.py 2>&1 | sed 's/np.float64(\([^)]*\))/\1/g' | cut -c1-260`

```
L=4 g=0.5 E=0.0 m=0.000000+0.698785j resid=2.2e-16 rowsum_dev=1.6e-15 kappa=0.6988
  tau=0 is delta: True; sum_a kBA(1)=1.000000000000 min=1.03e-02 max=0.1455
  max|series-Fourier| = 4.65e-15; Khat range [0.3411,1.0000]
  Lean c=9.444e-19; empirical min (1-Khat)/(g^2|th|^2)=0.0681 (>= Lean c: True)
  c'=24.702=0.95*L^2*min_{k!=0}(1-Khat)/g^2; gap ratios r1,r2,r3 = sup of lhs/rhs at c' [(16, 4.169, 11.028, 86.591), (32, 1.115, 2.972, 23.751), (64, 0.083, 0.221, 1.764)]
  diag_le empirical C = 0.889
  Laplace a=(0, 0, 0): Theta=1.5462698067 integral=1.5462698067
  Laplace a=(1, 0, 0): Theta=0.0624797081 integral=0.0624797081
  Laplace a=(1, 1, 2): Theta=0.0218013065 integral=0.0218013065
  semigroup max dev = 1.05e-15
L=4 g=2.0 E=0.3 m=-0.145132+0.546675j resid=4.3e-16 rowsum_dev=1.8e-15 kappa=0.5467
  tau=0 is delta: True; sum_a kBA(1)=1.000000000000 min=1.16e-04 max=0.8460
  max|series-Fourier| = 5.55e-16; Khat range [0.0228,1.0000]
  Lean c=5.780e-19; empirical min (1-Khat)/(g^2|th|^2)=0.0005 (>= Lean c: True)
  c'=0.239=0.95*L^2*min_{k!=0}(1-Khat)/g^2; gap ratios r1,r2,r3 = sup of lhs/rhs at c' [(16, 9.066, 39.948, 266.164), (32, 2.743, 14.761, 116.691), (64, 1.053, 8.002, 64.015)]
  diag_le empirical C = 5.110
  Laplace a=(0, 0, 0): Theta=1.4022051510 integral=1.4022051510
  Laplace a=(1, 0, 0): Theta=0.0094856024 integral=0.0094856024
  Laplace a=(1, 1, 2): Theta=0.0444655641 integral=0.0444655641
  semigroup max dev = 5.55e-16
L=6 g=0.5 E=0.0 m=0.000000+0.658961j resid=3.4e-16 rowsum_dev=2.2e-15 kappa=0.6590
  tau=0 is delta: True; sum_a kBA(1)=1.000000000000 min=2.15e-03 max=0.1153
  max|series-Fourier| = 1.44e-15; Khat range [0.2573,1.0000]
  Lean c=8.398e-19; empirical min (1-Khat)/(g^2|th|^2)=0.1003 (>= Lean c: True)
  c'=38.899=0.95*L^2*min_{k!=0}(1-Khat)/g^2; gap ratios r1,r2,r3 = sup of lhs/rhs at c' [(36, 0.775, 1.549, 9.294), (72, 0.1, 0.2, 1.2), (144, 0.002, 0.003, 0.02)]
  diag_le empirical C = 0.889
  Laplace a=(0, 0, 0): Theta=1.4554649938 integral=1.4554649938
  Laplace a=(1, 0, 0): Theta=0.0614509966 integral=0.0614509966
  Laplace a=(1, 1, 2): Theta=0.0083973257 integral=0.0083973257
  semigroup max dev = 7.22e-16
L=8 g=1.0 E=0.0 m=-0.000000+0.466463j resid=4.5e-16 rowsum_dev=2.6e-15 kappa=0.4665
  tau=0 is delta: True; sum_a kBA(1)=1.000000000000 min=2.55e-04 max=0.4587
  max|series-Fourier| = 8.88e-16; Khat range [0.0921,1.0000]
  Lean c=4.208e-19; empirical min (1-Khat)/(g^2|th|^2)=0.0202 (>= Lean c: True)
  c'=33.302=0.95*L^2*min_{k!=0}(1-Khat)/g^2; gap ratios r1,r2,r3 = sup of lhs/rhs at c' [(64, 2.152, 6.923, 43.525), (128, 0.361, 1.162, 7.685), (256, 0.011, 0.035, 0.231)]
  diag_le empirical C = 0.960
  Laplace a=(0, 0, 0): Theta=1.1864013752 integral=1.1864013752
  Laplace a=(1, 0, 0): Theta=0.0205102118 integral=0.0205102118
  Laplace a=(1, 1, 2): Theta=0.0075903631 integral=0.0075903631
  semigroup max dev = 1.67e-16
```

External hypotheses: none (no Step 0 external input; `BAK_gap`, `BAK_shift`, `BAK_pow_*` are merged Lean). Limit computation not applicable (no `∀ᶠ`, no asymptotic hypothesis).

### Verdict per target
- `BAP`, `kBA` (definitions): PASS (`P_0 = 1`, entire in `s`, `g>0` needed only for `τ/g²`).
- `BATheta_eq_laplace_kBA`: PASS (`0 ≤ t < 1`; identity checked to 10 digits at 12 points).
- `BAP_semigroup_shift`: PASS (Cauchy product of entire series; translation invariance from `BAK_pow_shift`, for all real `s`).
- `kBA_basic`: PASS (nonneg/≤1/mass from `BAK_pow_nonneg`, `BAK_pow_row_sum`; evenness and continuity from the series/Fourier form).
- `kBA_fourier`: PASS (all real `τ`, `g>0`; no `BASelf` needed).
- `kBA_diag_le`: PASS (`C` depends on `(d,Λ,κ)`; numeric sup `0.89/5.1/0.89/0.96`).
- `kBA_gap`: PASS (exponents `d, d+1, d+2` close exactly at `τ ≥ L²`; no loss, no `g`-`L` relation).

### (a′) Preflight corrections — Thu Oct  8 12:32:49 UTC 2026
No verdict changes. Two rows of (a)(i) differ from what the Lean proof uses (the targets keep `∃ C c`, so nothing pinned moves):
- "gap, value": `c = 2π²c_g` is the rate of the zero-mode inequality alone. The Lean proof uses one `c = π² c_g` for all three inequalities (split `e^{-wΘ} = e^{-wΘ/2} e^{-wΘ/4} e^{-wΘ/4}`, `KHeat_master`), with `C = T₁^d (1 + (1/c_g + 1) + 2/c_g)`, `T₁ = 1 + 2r/(1-r)`, `r = e^{-π² c_g}`.
- "diag-bound sum": the explicit `L^{-1} + (4π c_g τ)^{-1/2}` bound is not used. The Lean proof dominates the Gaussian sum by `Heat.hkT L (c_g τ) 0` (`1 - cos θ ≤ θ²/2`) and takes `Heat.hkT_le` (`w ≤ L²`) / `Heat.hkT_gap` (`w ≥ L²`); `C₁, C₂` are existential.

## (b) Script output (stage 1b; scripts and scratch files in the T2331/ scratchpad directory)

$ date -u; git log -1 --format=%h; git diff --stat main...t/T2331; git status --short; wc -l RBM3D/BA/KHeat.lean; grep -cE "sorry|admit|native_decide|^axiom" RBM3D/BA/KHeat.lean
Thu Oct  8 12:30:52 UTC 2026
adff21c
 RBM3D/BA/KHeat.lean | 1420 +++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1420 insertions(+)
    1420 RBM3D/BA/KHeat.lean
0
$ lake build RBM3D.BA.KHeat 2>&1 | grep -E "KHeat|Build completed|error"
Build completed successfully (3741 jobs).
$ lake env lean axioms.lean   (#print axioms of the six targets; scratch file = import RBM3D.BA.KHeat + six #print axioms)
'RBM.BA.BATheta_eq_laplace_kBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAP_semigroup_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_basic' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_fourier' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
$ registry pre-check: lake env lean registry.lean   (import RBM3D; import RBM3D.BA.KHeat; #assert_rbm_axioms)
[exit 0]
axiom audit: 9943 theorems, 2978 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ full `lake build` with a temporary uncommitted `import RBM3D.BA.KHeat` after the last import of RBM3D.lean (restored afterwards)
Thu Oct  8 12:31:39 UTC 2026
[exit 0]
Build completed successfully (4140 jobs).
Thu Oct  8 12:31:41 UTC 2026
$ git status --short   (after restoring RBM3D.lean)
$ check-file equality (a): python3 -I cmp.py (definitions and six statements, whitespace-normalized)
BAP, kBA definitions equal: True
BATheta_eq_laplace_kBA statement equal: True
BAP_semigroup_shift statement equal: True
kBA_basic statement equal: True
kBA_fourier statement equal: True
kBA_diag_le statement equal: True
kBA_gap statement equal: True
$ check-file equality (b): lake env lean checkeq.lean  (check file + import RBM3D.BA.KHeat + six `example : T2331Check.T2331_X := RBM.BA.X`)
[exit 0]
0
6
$ name-clash grep: whole-word hits of all new public names in RBM3D/ outside Probe/ and KHeat.lean
       0
$ grep -n "RBM1D\|RBM2D" RBM3D/BA/KHeat.lean   (ports from sister projects)
23:(`KSymbol.lean:610`).  Nothing is ported from `../RBM1D` or `../RBM2D`.  The semigroup 
$ target statements, extracted by awk from RBM3D/BA/KHeat.lean
def BAP (g E : ℝ) (m : ℂ) (s : ℝ) (a b : Zd d L) : ℝ :=
  Real.exp (-s) * ∑' n : ℕ, s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) a b
def kBA (g E : ℝ) (m : ℂ) (τ : ℝ) (a : Zd d L) : ℝ :=
  BAP d L g E m (τ / g ^ 2) 0 a
theorem BATheta_eq_laplace_kBA : ∀ (d L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ) (t : ℝ), 0 < g → BASelf d L g (E : ℂ) m →
    0 ≤ t → t < 1 → ∀ a : Zd d L,
      BATheta d L g E m t true false 0 a =
        ((∫ u in Ioi (0 : ℝ), Real.exp (-(1 - t) * u) * kBA d L g E m (t * g ^ 2 * u) a : ℝ) : ℂ) := by
theorem BAP_semigroup_shift : ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m →
    (∀ s s' : ℝ, 0 ≤ s → 0 ≤ s' → ∀ a b : Zd d L,
      BAP d L g E m (s + s') a b = ∑ c : Zd d L, BAP d L g E m s a c * BAP d L g E m s' c b) ∧
    (∀ s : ℝ, ∀ a b : Zd d L, BAP d L g E m s a b = BAP d L g E m s 0 (b - a)) := by
theorem kBA_basic : ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), 0 < g → BASelf d L g (E : ℂ) m →
    (∀ τ : ℝ, 0 ≤ τ → ∀ a : Zd d L, 0 ≤ kBA d L g E m τ a) ∧
    (∀ τ : ℝ, 0 ≤ τ → ∑ a : Zd d L, kBA d L g E m τ a = 1) ∧
    (∀ τ : ℝ, 0 ≤ τ → ∀ a : Zd d L, kBA d L g E m τ a ≤ 1) ∧
    (∀ a : Zd d L, kBA d L g E m 0 a = if a = 0 then 1 else 0) ∧
    (∀ τ : ℝ, ∀ a : Zd d L, kBA d L g E m τ (-a) = kBA d L g E m τ a) ∧
    (∀ a : Zd d L, Continuous fun τ : ℝ => kBA d L g E m τ a) := by
theorem kBA_fourier : ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), 0 < g → ∀ (τ : ℝ) (a : Zd d L),
    kBA d L g E m τ a = (((L : ℝ) ^ d)⁻¹) * ∑ k : Zd d L,
      Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) *
        Real.cos (2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ)) := by
theorem kBA_diag_le : ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → ∀ a : Zd d L,
        kBA d L g E m τ a ≤ C * (min 1 (τ ^ (-(d : ℝ) / 2)) + ((L : ℝ) ^ d)⁻¹) := by
theorem kBA_gap : ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ (a : Zd d L) (i j : Fin d),
        |kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹| ≤ C * ((L : ℝ) ^ d)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
        |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
          ≤ C * ((L : ℝ) ^ (d + 1))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
        |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
            - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
          ≤ C * ((L : ℝ) ^ (d + 2))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) := by
$ compiled nonempty instances (namespace RBM.BA.KHeatInst, flow point P: d = 3, L = 4, Lambda = 10); selected, extracted by awk
theorem inst_zero_delta :
    ∀ a : Zd 3 4, kBA 3 4 P.g0 P.E P.m0 0 a = if a = 0 then 1 else 0 :=
theorem inst_mass : ∑ a : Zd 3 4, kBA 3 4 P.g0 P.E P.m0 1 a = 1 :=
theorem inst_laplace :
    BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![1, 0, 0]
      = ((∫ u in Ioi (0 : ℝ), Real.exp (-(1 - 1 / 2) * u)
          * kBA 3 4 P.g0 P.E P.m0 (1 / 2 * P.g0 ^ 2 * u) ![1, 0, 0] : ℝ) : ℂ) :=
theorem inst_diag_le :
    ∃ C : ℝ, 0 < C ∧
      kBA 3 4 P.g0 P.E P.m0 4 0 ≤ C * (min 1 ((4 : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)) + (((4 : ℕ) : ℝ) ^ 3)⁻¹) := by
theorem inst_gap :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      (|kBA 3 4 P.g0 P.E P.m0 16 ![1, 0, 2] - (((4 : ℕ) : ℝ) ^ 3)⁻¹|
          ≤ C * (((4 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-c * 16 / ((4 : ℕ) : ℝ) ^ 2) ∧
        |kBA 3 4 P.g0 P.E P.m0 16 (![1, 0, 2] + Pi.single 2 1) - kBA 3 4 P.g0 P.E P.m0 16 ![1, 0, 2]|
          ≤ C * (((4 : ℕ) : ℝ) ^ (3 + 1))⁻¹ * Real.exp (-c * 16 / ((4 : ℕ) : ℝ) ^ 2) ∧
        |kBA 3 4 P.g0 P.E P.m0 16 (![1, 0, 2] + Pi.single 0 1 + Pi.single 2 1)
            - kBA 3 4 P.g0 P.E P.m0 16 (![1, 0, 2] + Pi.single 0 1)
            - kBA 3 4 P.g0 P.E P.m0 16 (![1, 0, 2] + Pi.single 2 1)
            + kBA 3 4 P.g0 P.E P.m0 16 ![1, 0, 2]|
          ≤ C * (((4 : ℕ) : ℝ) ^ (3 + 2))⁻¹ * Real.exp (-c * 16 / ((4 : ℕ) : ℝ) ^ 2)) := by
$ grep -o "^theorem inst_[a-z_]*" RBM3D/BA/KHeat.lean | sed s/theorem//
inst_zero_delta inst_zero_origin inst_zero_off inst_mass inst_nonneg_le_one inst_even inst_continuous inst_fourier inst_semigroup inst_shift inst_laplace inst_laplace_origin inst_diag_le inst_gap inst_gap_diag 

### Narrative (facts from the file and the logs above)
- Delivered: the two definitions and the six targets, in the sole file `RBM3D/BA/KHeat.lean` (1420 lines, namespace `RBM.BA`), commit `adff21c` on `t/T2331`. Definitions and statements equal the check file (script above); no hypothesis added, weakened or reordered.
- Imports: `RBM3D.BA.KSymbol`, `RBM3D.Propagator.HeatProduct`, and `Mathlib.Analysis.Normed.Algebra.MatrixExponential` (only for `Matrix.exp_add_of_commute` in `BAP_semigroup_shift`).
- Fourier form (`kBA_fourier`): `K` is circulant (`BAK_shift`) and even; with `χ_k(a) = stdAddChar(Σ_j k_j a_j)`, `Σ_b K(a,b) χ_k(b) = χ_k(a) K̂(k)` (`BAKhat_eq`) and `Σ_k χ_k(b) = L^d [b = 0]`, hence `(Kⁿ)(0,a) = L^{-d} Σ_k K̂(k)ⁿ cos(θ_k·a)` (`KHeat_pow_fourier`), then the exponential series. No `BASelf`, all real `τ`.
- Semigroup: `BAP s a b = e^{-s} · (NormedSpace.exp (s • K)) a b` (`KHeat_exp_apply`, via `Pi.tsum_apply`), then `Matrix.exp_add_of_commute`. The proof ignores the hypotheses `0 ≤ s`, `0 ≤ s'` of the pinned statement. Translation invariance: termwise `BAK_pow_shift`.
- Laplace: Neumann series `Ring.inverse (1 - tK) = (Σ' tⁿ (Kⁿ)(a,b))_{ab}` from `(1 - tK) B = 1` (`KHeat_neumann`, `KHeat_Theta_eq`) and `BATheta_pm_eq`; then `∫_{Ioi 0} e^{-u} uⁿ/n! du = 1` (`KHeat_gamma`), `integral_tsum_of_summable_integral_norm`, and `t g² u / g² = t u`.
- Basic properties: `0 ≤ kBA ≤ 1`, mass `1` from `BAK_pow_nonneg`, `BAK_pow_row_sum`; `δ_0` at `τ = 0` (`BAP_zero`); evenness from `BAK_pow_shift` and `BAK_pow_transpose`; continuity from the Fourier form (`fun_prop`).
- Diag bound: `kBA ≤ L^{-d} Σ_k e^{-c_g τ |θ_k|²}` (`BAK_gap`, `|cos| ≤ 1`), factorised over coordinates (`KHeat_prod_sum`); the 1D factor is bounded as in (a′); `(x+y)^d ≤ 2^d (x^d + y^d)`; the case `τ ≤ 1` uses `kBA ≤ 1`.
- Regime (ii): the `k = 0` term is `L^{-d}` (`KHeat_Khat_zero`); the unit differences vanish at `k = 0`. For `k ≠ 0`, `|θ_k|² ≥ (2π/L)²` (`KHeat_thetaSq_ge`), `|e^{2πi y/L} - 1| ≤ 2π |y|_L / L` (`KHeat_char_sub_one`), `θ_i θ_j ≤ |θ_k|²`, and `KHeat_master` sums the tail; `KHeat_poly1`, `KHeat_poly2` give the factors `L^{-1}`, `L^{-2}` from `τ ≥ L²`.
- Copies of private RBM3D lemmas (re-proved, not imported): `sum_geom_zdist` (`HeatTorus1D.lean:354`), `mul_exp_neg_le_one` (`HeatTorus1D.lean:299`), `KSymbol_cos_zdist` (`KSymbol.lean:610`), orthogonality of the exponentials (`HeatProduct.lean:858`, `AddChar` form). No port from `../RBM1D`/`../RBM2D` (grep above), so no sister-project diff-stat applies.
- Instances: every target is applied in `RBM.BA.KHeatInst` at the flow point `P` of `MFixedPointInst` (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`), with `P.g0_pos`, `P.g0_le`, `P.real`, `P.real.1` (`BASelf`), `3 ≤ 4`, `0 ≤ t < 1` discharged; no hypothesis left open. The instances the ticket asks for: `inst_zero_delta` (`τ = 0`), `inst_mass` (`Σ_a kBA 1 a = 1`), `inst_gap` (`τ = 16 = L²`).
- `lake build RBM3D.BA.KHeat`, the registry pre-check and the full `lake build` with the temporary import pass (output above). The first run of the temporary-import full build took 12:27:12 → 12:27:54 per `date -u` (tool log) and rebuilt `RBM3D.lean` with `#assert_rbm_axioms`; the run above is cached.

## (c) Verified Mathlib names (`#check` on this commit; used in `KHeat.lean`)
`NormedSpace.expSeries_div_hasSum_exp`, `Real.exp_eq_exp_ℝ`, `NormedSpace.exp_eq_tsum`: exponential series; `Real.summable_pow_div_factorial`; `Real.exp_nat_mul`
`Matrix.exp_add_of_commute` (import `Mathlib.Analysis.Normed.Algebra.MatrixExponential`): semigroup law
`Pi.tsum_apply`, `Pi.summable`: entries of a matrix-valued series (the matrix type needs `change` to match)
`Summable.tsum_finsetSum`, `Summable.tsum_eq_zero_add`, `tsum_mul_left`, `tsum_mul_right`, `Summable.of_norm_bounded`, `Summable.of_nonneg_of_le`, `summable_geometric_of_lt_one`
`mul_eq_one_comm` (root, `IsDedekindFiniteMonoid`) and `Ring.inverse_mul_cancel`: `(1 - tK) B = 1 → Ring.inverse (1 - tK) = B`
`Real.GammaIntegral_convergent`, `Real.Gamma_eq_integral`, `Real.Gamma_nat_eq_factorial`, `MeasureTheory.integral_tsum_of_summable_integral_norm`: the Gamma integral and the swap
`ZMod.stdAddChar_coe`, `ZMod.isPrimitive_stdAddChar`, `ZMod.card`, `AddChar.sum_mulShift`, `AddChar.map_add_eq_mul`, `Fintype.prod_sum`: characters and orthogonality
`ZMod.valMinAbs_natAbs_eq_min`, `ZMod.coe_valMinAbs`: integer representative of `|y|_L`
`Real.norm_exp_I_mul_ofReal_sub_one_le` (namespace `Real`), `Real.one_sub_sq_div_two_le_cos`, `Complex.exp_ofReal_mul_I_re`, `Complex.norm_exp_ofReal_mul_I`, `Complex.abs_re_le_norm`, `Complex.re_le_norm`
`Real.exp_lt_one_iff`, `Real.exp_le_one_iff`, `Real.mul_rpow`, `Real.rpow_natCast`, `Real.one_le_rpow_of_pos_of_le_one_of_nonpos`, `Real.rpow_le_one_of_one_le_of_nonpos`, `pow_le_pow_iff_left₀`, `div_le_div₀`
`Finset.abs_sum_le_sum_abs`, `Finset.sum_le_sum_of_subset_of_nonneg`
Verified absent (unknown identifier on this commit): `Matrix.mul_eq_one_comm`, `Matrix.tsum_apply`, `tsum_apply` (root), `Real.exp_lt_one`, `AddChar.map_sum_eq_prod` (proved `KHeat_char_sum`), `Complex.norm_exp_I_mul_ofReal_sub_one_le`, `isUnit_of_mul_eq_one` (used `⟨⟨_, B, _, _⟩, rfl⟩`).

## (d) Open issues and paper-delta candidates
- Paper-delta candidate `T2331a`: the Poisson semigroup `P_s`, the diffusive time `τ = g² s`, the Laplace identity and regime (ii) `τ ≥ L²` are Lean-side design (supervisor 1048 C1/C2); `A_deterministic_estimates.tex` has only the discrete Neumann series (lines 16-20) and a random-walk sketch (lines 58-66). The statements are the pinned ones; no Lean/paper difference beyond this.
- Registry: none owed by this row; `BAProp5…8` stay owed until P5/P6/P8. Not done by design: `kBA_le` (regime (i), P4b) and the regime-(i) differences (P4c).
- Public helpers for stage K / P4b: `BAP_nonneg`, `BAP_row_sum`, `BAP_le_one`, `BAP_shift`, `BAP_neg`, `BAP_zero` (hypotheses as in each signature); `kBA_fourier` holds for every real `τ` without `BASelf`.
- Constants are existential and not optimised (`c = π² c_g`, `c_g` from `BAK_gap`, which is `9.4e-19` at `L = 4`, `g = 0.5` in (a)); the numeric ratios of (a)(ii) use the true rate.
