Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 20:28:05 UTC 2026

Sources: RBM2D `Path/StepDecomp.lean` at `c9a24cf` (1553 lines), merged `RBM3D/Gauss/FineModel.lean`, `RBM3D/Path/{Walk,Markov}.lean`, `RBM3D/Defs/{Sizes,Block}.lean`. Scripts: scratchpad `T2073/check.py`, `T2073/check2.py` (python/numpy, no Lean).

Restatement (mathematics only). `Φ_a`, `a ∈ Z_L^d × Z_L^d`, real on Hermitian matrices, `U(b,a) ∈ ℝ`, `H_j = √s X_0 + √Δ Σ_{i=1}^j X_i`, `Δ = (t-s)/K`.
`ξ_b = Σ_a U Φ_a(H_{j+1}) − E[· | F_j]`, `Z_b = √Δ · Re tr(A_b X_{j+1})`, `A_b = Σ_a U(b,a) gradMat(Φ_a)(H_j)`, `Y_b = ξ_b − Z_b`.
`stepDecomp`: `ξ = Z + Y`; `A_b` is `F_j`-measurable; `‖Y‖ ≤ g + E[g|F_j]`, `g = (Σ_a|U(b,a)|)(C₂/2)Δ‖X_{j+1}‖²`; `E[Y|F_j] = 0`.
`stepDecomp_Z_subG`: on an `F_j`-event `E` with `Δ·linTrVar(A_b) ≤ c`, `Z·1_E` is conditionally sub-Gaussian with parameter `c`.

### (i) Exponent table

| # | Quantity (RBM2D line at `c9a24cf`) | `d=2` form | `d ≥ 3` replacement | Constraint | Slack / status |
|---|---|---|---|---|---|
| 1 | lattice index `Z2 L`, `Idx L W` (labels `a`, 90 lines with `Z2 (d.L n)`; 459 `simp [Idx, Z2, pow_two]`) | `Z_L^2`, `Fin 2 → ZMod` | `Zd d L`, `Idx d L W`; `card Idx = (W L)^d = sz.size n` (`Sizes.card_Idx`, `Sizes.lean:160`) | labels finite: `|Z_L^d|² = L^{2d}` | statements carry no `d`-power; labels only appear in finite sums. `d=3,L=3`: 27 sites, 729 labels |
| 2 | `N = (W L)^2` (367, 371, 452–459, 591–623, 674–685) | `(W L)²` | `N = (W L)^d = sz.size n` | `card CoordF = 2 N²` | exact: `CoordF = Idx × Idx × Bool`; script: `#Coord = 93312 = 2·216²` |
| 3 | `E‖X‖² ≤ 16 N⁴` (591, 604, 677) | `N = (W L)²` | `16 N⁴`, `N = (W L)^d` unchanged | `‖X‖ ≤ 2Σ_c|ω_c|`, Cauchy–Schwarz with `#Coord = 2N²`, `E ω_c² = gvarF ≤ 1` | no `d` in the constant. Script: `E‖X‖² ≈ 3.94 ≤ 3.5e10` |
| 4 | `E‖X‖⁴ ≤ 768 N⁸` (609, 623, 685) | same | `768 N⁸` unchanged | `16·(2N²)³·3 = 768 N⁶·N²`; `E x⁴ = 3 v² ≤ 3` for `v ≤ 1` | script: `E‖X‖⁴ ≈ 15.5 ≤ 3.6e21` |
| 5 | `gvar ≤ 1` (439–448: five-point `svar`, `(W⁻¹)² ≤ 1`) | `svar ≤ 1` from profile | `svarF = (W^d)⁻¹ · SBR(blk i − blk j)`, `SBR = a·1[x=0] + b·1[\|x\|=1]`, `a = (1+2dg²)⁻¹`, `b = g²a` (`Block.lean:74`); the two pieces have disjoint support, so `svarF ≤ W^{-d} max(a,b)`; `max(a,b) ≤ 1` since `a ≤ 1`, `b ≤ 1/(2d)`; `gvarF ≤ svarF` | `W ≥ 1` (`NeZero W`), `g` real | `d=3,W=2,g=1/2`: `max gvarF = 0.05 ≤ 1` (slack 0.95). **Replaced proof** (merged `svarF` carries `g`, not the fixed profile; DECISIONS §30) |
| 6 | row sum `Σ_j S_ij` | `=1` | `a + 2d·b = 1` (`sum_sbKernelR`, needs `3 ≤ L`); `Σ_j S_ij = 1` | `3 ≤ L` | script: row sums min = max = 1.0 at `L=3`. Not used by the targets except in the constant of row 8 |
| 7 | `C₂` in `hC₂` (Taylor, `‖fderiv² Φ M y y‖ ≤ C₂‖y‖²`) | input | input, dimension-free | `C₂ ≥ 0` unconstrained | instance `Φ = sin Re tr`, `C₂ = ‖Re tr‖² = N² = 46656` (`\|Re tr A\| ≤ N‖A‖_op`, equality at `A = 1`) |
| 8 | sub-Gaussian proxy `c` of `stepDecomp_Z_subG` (`d`-dim. constant) | input `c ≥ Δ·linTrVar(A_b)` | for Hermitian `A`: `linTrVar(A) = Σ_{ij} S_ij\|A_ij\|²` ≤ `W^{-d} max(a,b)·‖A‖_HS² ≤ L^d max(a,b)‖A‖²_op`; `A = 1`: `linTrVar(1) = Σ_i S_ii = L^d/(1+2dg²)` (`d=2`: `L²/(1+4g²)`; `d=3`: `L³/(1+6g²)`) | `c ≥ 0`, `Δ·linTrVar(A_b) ≤ c` on `E` | the hypothesis `c` is not computed inside the lemma. `d=3`: `L³/(1+6g²) = 10.8` exact (script). The constant depends on `d`, `L`, `g` through `1+2dg²` and `L^d`, not on `W` |
| 9 | `W` in `W^{-2}`-type | (none in the statements) | none; `W` enters only through `S_ij = W^{-d}·SBR` (rows 5, 8) | – | – |

Boundary checks (DECISIONS §29; none of the four items is used by the targets):
(1) time domain: `s, t, K` free reals/naturals; `pathH` uses `√(s n)` and `√Δ`; `stepDecomp` needs only `hΔ : 0 ≤ Δ`; `0 ≤ s`, `t < 1`, `t ≤ lemT` are not used (`pathH_isHermitian`, `Walk.lean:97`, holds for all `s, t, K`). `stepDecomp_Z_subG` has no `hΔ` (`hasCondSubgaussianMGF_linear` uses `√Δ`, which is 0 for `Δ ≤ 0`).
(2) case-(ii) boundary `1 − ilambda²/L²`: no spectral or flow time appears; not used.
(3) `L^d ≤ W^K`: not used; no relation between `L`, `W` besides `NeZero`. (4) `∀ n` vs `∀ᶠ n`: fixed `n`, `j`; no `∀ n` over a sequence in any target.

### (ii) Concrete nondegenerate instance (d = 3, L = 3, W = 2)

Data: `d=3`, `L=3`, `W=2`, `N = 216`, `lam = g = 1/2` (satisfies `W^{-d/2+𝔡} = 0.379 ≤ 1/2 ≤ 10 = 𝔡⁻¹` at `𝔡 = 1/10`; not a hypothesis of the targets), window `s = 0.2`, `t = 0.6`, `K = 8`, `Δ = 0.05`, `j = 3`, `Φ_a(A) = sin(Re tr A)` for all `a`, `U(b,a) = 1[a=b]` (so `Σ_a|U| = 1`), `C₂ = 46656`.
Hypotheses checked at once: `HermTestFun` (C² at Hermitian points; `|Φ| ≤ 1`), `hReal` (`Φ` real), `hC₂` with `C₂ = N²`, `hΔ: Δ = 0.05 ≥ 0`; `E = univ` (`F_j`-measurable), `c = Δ·linTrVar(1) = 0.54 ≥ 0`; `hbound: Δ·linTrVar(cos(Re tr H_j)·1) ≤ c`. The model `S_ij` is built exactly as `svarF` (block = `val / W` per coordinate, `zdistD` on `Z_3^3` with 6 neighbours, `d=3`).
In the instance `gradMat = cos(Re tr M)·1`, so `A_b = cos(Re tr H_j)·1` (nonzero: `cos = 0.476` at the sample).

Commands (outputs verbatim below; `T2073/` = scratchpad subdirectory):
`python3 check.py` and `python3 check2.py` (8.96 s total).

```
N = 216  #Coord = 2N^2 = 93312  row sums of S (should be 1): 1.0 1.0
max gvarF (diag S_ii, offdiag S_ij/2) <= 1: 0.05  1+2dg^2 = 2.5
H_j Hermitian: True  H_{j+1}-H_j = sqrt(D) X_{j+1}: True
gradMat check, Phi=sin Re tr: max entry err = 1.70e-11 ; Phi=sin(Re tr A^2/N): 4.75e-11
fderiv(X) = Re tr(gradMat X) for Hermitian X, |diff| = 4.66e-11
linTrVar(1) = sum S_ii = 10.800000 ; L^d/(1+2 d g^2) = 10.800000
xi = -0.918241, Z = -0.630271, Y = -0.287970, xi-Z-Y = 0.0e+00
|Y| = 0.287970 <= g = 4749 (+E g <= 4.062e+13): True
cos(Re tr H_j) = 0.4760; proxy Delta*linTrVar(Ab) = 0.12233; hypothesis c = Delta*linTrVar(1) = 0.54000
empirical Var Z = 0.12635 (exact 0.12233), mean Z = -0.0035
  lambda= 0.25  E exp(lam Z) =     1.0031  <=  exp(lam^2 c/2) =     1.0170 : True
  lambda= 0.50  E exp(lam Z) =     1.0141  <=  exp(lam^2 c/2) =     1.0698 : True
  lambda= 1.00  E exp(lam Z) =     1.0612  <=  exp(lam^2 c/2) =     1.3100 : True
  lambda= 2.00  E exp(lam Z) =     1.2766  <=  exp(lam^2 c/2) =     2.9447 : True
  lambda= 4.00  E exp(lam Z) =     2.6804  <=  exp(lam^2 c/2) =    75.1886 : True
  lambda= 8.00  E exp(lam Z) =    45.5563  <=  exp(lam^2 c/2) = 31960138.1039 : True
empirical sub-Gaussian constant sigma^2 = max_{lam} 2 log E exp(lam Z)/lam^2 over the grid: 0.12324376454966225  vs c = 0.12233429896014877  c_hyp = 0.54
E[Y|F_j] ~ mean Y = -3.70e-03 (std err 2.84e-03); mean of Y*1 over samples
E||X||_op^2 (200 samples) = 3.94 <= 16 N^4 = 3.48e+10 ; E||X||^4 = 15.54 <= 768 N^8 = 3.64e+21
linTrVar(A) from coordinate coefficients = 212.99072406 ; sum_ij S_ij |A_ij|^2 = 212.99072406
bound  W^-d max(a,b) ||A||_HS^2 = 2323.636438 ; N W^-d max(a,b) ||A||_op^2 = L^d max(a,b) ||A||_op^2 = 9124.738194
max(a,b) = 0.4000 (a = (1+2dg^2)^-1, b = g^2 a); a+2d b = 1.0000
```

Reading of the output. The `10⁴` samples are draws of `X_{j+1}` at the fixed sample `H_j` (conditioning on `F_j`); the conditional mean `E[Φ(H_{j+1})|F_j] = sin(Re tr H_j) e^{-Δ v/2}`, `v = linTrVar(1) = 10.8`, is exact (Re tr X ~ N(0, v)). The true proxy of `Z` is `Δ linTrVar(A_b) = 0.12233` (equality: `Z` is exactly Gaussian, empirical `0.1232`, within sampling error); the hypothesis value `c = 0.54` has slack factor `4.4`. `E[Y|F_j]` is zero within `1.3` standard errors. The pathwise bound `|Y| ≤ g` holds with slack factor `~1.6·10⁴` (the constant `C₂ = N²` is crude, valid). The moment bounds hold with slack `~10⁹`, `~10²⁰`.

No external hypothesis occurs in the four targets (no limit computation needed). The only non-pinned data are `HermTestFun`/`hC₂`/`hReal` (concrete above).

Not proved by numerics (paper-level or Lean-level, left to stage 1b): the Lean `ξ = Z + Y` is the definition `Y := ξ − Z`, and the real content is the `E[Y|F_j] = 0` and `‖Y‖` bound, checked above at one `H_j`.

### Verdict

| Target | Verdict | Reason |
|---|---|---|
| `gradMat` | PASS | dimension-free definition on `Matrix ι ι ℂ`; `gradMat = cos(Re tr M)·1` and `fderiv X = Re tr(gradMat X)` verified at `d=3` (err `4.7e-11`) |
| `HermTestFun` | PASS | dimension-free structure; `sin Re tr` satisfies (H1)–(H2), `C₂ = N²` for (H3) |
| `stepDecomp` | PASS | all hypotheses hold at the instance; identity and `E[Y|F_j]≈0` at `d=3`; the only `d`-dependent count is `#Coord = 2N²`, `N = (W L)^d` (rows 2–5) |
| `stepDecomp_Z_subG` | PASS | `c` is a hypothesis; the `d=3` constant is `linTrVar(1) = L³/(1+6g²)`, general `linTrVar(A) = Σ S_ij\|A_ij\|²` (row 8) |

Stage 1b notes (mathematics): the one proof that changes is row 5 (`gvarF ≤ 1` from `svarF`, not from the fixed profile); `StepDecomp_card_Coord` becomes `2 (card Idx)²` with `card Idx = sz.size n` (`Sizes.card_Idx`).

## (b) Script output — Sat Oct  3 20:35:07 UTC 2026 (commits 4a267f4, 1790985 on t/T2073, worktree RBM3D-wt/T2073)

### b.1 Builds (worktree T2073)
```
$ lake build RBM3D.Path.StepDecomp 2>&1 | tail -1
Build completed successfully (3316 jobs).
$ lake build 2>&1 | tail -1   (full library, run after the Axioms.lean edit)
Build completed successfully (3792 jobs).
$ grep -c "sorry|admit|native_decide|^axiom" RBM3D/Path/StepDecomp.lean
0
$ wc -l RBM3D/Path/StepDecomp.lean
    1602 RBM3D/Path/StepDecomp.lean
```

### b.2 Registry pre-check (DECISIONS §20; scratch file outside the repository)
```
$ cat scratchpad/T2073/precheck.lean
import RBM3D
import RBM3D.Path.StepDecomp

#assert_rbm_axioms
$ lake env lean scratchpad/T2073/precheck.lean 2>&1 | tail -4 ; exit code
exit=0
98:premises found by scanning: 82 (borrowed 2, owed 66, structural 14).
99:registry: 5 borrowed + 86 owed + 36 structural; 45 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
 RBM.Graph.NGraph.NoGhost,
 RBM.Graph.NGraph.GhostOK].
non-vacuity certificates: 4 of 91 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
$ git diff main...t/T2073 --stat
 RBM3D/Path/StepDecomp.lean | 1602 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |    1 +
 2 files changed, 1603 insertions(+)
```

### b.3 Axioms (`lake env lean scratchpad/T2073/axioms.lean`)
```
'RBM.Path.gradMat' [propext, Classical.choice, Quot.sound]
'RBM.Path.fderiv_eq_trace_gradMat' [propext, Classical.choice, Quot.sound]
'RBM.Path.lin_eq_fderiv' [propext, Classical.choice, Quot.sound]
'RBM.Path.HermTestFun' [propext, Classical.choice, Quot.sound]
'RBM.Path.integrable_normSq_incr' [propext, Classical.choice, Quot.sound]
'RBM.Path.integrable_normPow4_incr' [propext, Classical.choice, Quot.sound]
'RBM.Path.integral_normSq_incr_le' [propext, Classical.choice, Quot.sound]
'RBM.Path.integral_normPow4_incr_le' [propext, Classical.choice, Quot.sound]
'RBM.Path.Ab' [propext, Classical.choice, Quot.sound]
'RBM.Path.stepZ' [propext, Classical.choice, Quot.sound]
'RBM.Path.stepXi' [propext, Classical.choice, Quot.sound]
'RBM.Path.stepY' [propext, Classical.choice, Quot.sound]
'RBM.Path.stepDecomp' [propext, Classical.choice, Quot.sound]
'RBM.Path.stepDecomp_Y_sq' [propext, Classical.choice, Quot.sound]
'RBM.Path.stepDecomp_Z_subG' [propext, Classical.choice, Quot.sound]
'RBM.Path.stepDecomp_integrable_stepZ' [propext, Classical.choice, Quot.sound]
'RBM.Path.StepDecomp_check_stepDecomp' [propext, Classical.choice, Quot.sound]
'RBM.Path.StepDecomp_check_Z_subG' [propext, Classical.choice, Quot.sound]
'RBM.Path.StepDecomp_check_trace_not_hermTestFun' [propext, Classical.choice, Quot.sound]
```

### b.4 Target statements, extracted by script (`python3 scratchpad/T2073/extract.py`)
```
== gradMat: IDENTICAL after renaming (R1-R3)
== HermTestFun: IDENTICAL after renaming (R1-R3)
== stepDecomp: IDENTICAL after renaming (R1-R3)
== stepDecomp_Z_subG: IDENTICAL after renaming (R1-R3)
== stepDecomp_Y_sq: IDENTICAL after renaming (R1-R3)
== stepDecomp_integrable_stepZ: IDENTICAL after renaming (R1-R3)
== integral_normSq_incr_le: IDENTICAL after renaming (R1-R3)
== integral_normPow4_incr_le: IDENTICAL after renaming (R1-R3)

def gradMat (Φ : Matrix ι ι ℂ → ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ

structure HermTestFun {d : ℕ} (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) : Prop

theorem stepDecomp {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (hIntReal : Integrable (stepZ sz s t K n j Φ U b) (pathP sz)) :
    (∀ ω, stepXi sz s t K n j Φ U b ω
        = (stepZ sz s t K n j Φ U b ω : ℂ) + stepY sz s t K n j Φ U b ω)
      ∧ Measurable[filt sz j] (fun ω => Ab sz s t K n j Φ U b ω)
      ∧ (∀ᵐ ω ∂(pathP sz), ‖stepY sz s t K n j Φ U b ω‖
          ≤ (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
              * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2
            + (pathP sz)[fun ω' => (∑ a : Zd d (sz.L n) × Zd d (sz.L n), |U b a|) * ((C₂ / 2) * gridStep s t K n)
                * ‖Sizes.seqXmat sz n (ω' (j + 1))‖ ^ 2 | filt sz j] ω)
      ∧ (pathP sz)[stepY sz s t K n j Φ U b | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ)

theorem stepDecomp_Z_subG {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (E : Set (PathΩ sz)) (hE : MeasurableSet[filt sz j] E) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ ω ∈ E, gridStep s t K n * linTrVar n (Ab sz s t K n j Φ U b ω) ≤ c) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
      (fun ω => E.indicator (fun ω => stepZ sz s t K n j Φ U b ω) ω) ⟨c, hc⟩ (pathP sz)

```

### b.5 Compiled nonempty instances (d = 3, merged `sz0`: L 0 = 4, W 0 = 32, N = 2097152, lam 0 = 1/64; window s = 1/4, t = 3/4, K = 2, Δ = 1/4, j = 0, b = 0)
```
$ sed -n "/^section Instances/,/^end Instances/p" RBM3D/Path/StepDecomp.lean
section Instances

open RBM.Gauss.SizesInst

/-- The hypotheses of `stepDecomp` at the merged instance `sz0` (`d = 3`, `L 0 = 4`, `W 0 = 32`,
`N = 2097152`): `Φ_a = sin (Re tr)` for every label, `U = 1` on the diagonal, `C₂ = ‖Re tr‖²`, grid
`s = 1/4`, `t = 3/4`, `K = 2` (`Δ = 1/4`), step `j = 0`, label `b = 0`: `stepDecomp` applies with
every hypothesis discharged; the gradient matrix is `cos (Re tr M) • 1` (`StepDecomp_check_gradMat`). -/
example :=
  stepDecomp sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
    (Φ := StepDecomp_checkΦ sz0 0) (StepDecomp_check_class sz0 0)
    (fun a A _ => Complex.ofReal_im _)
    (C₂ := ‖StepDecomp_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2)
    (fun a M y _ _ => StepDecomp_check_hC₂ sz0 0 a M y) (by norm_num [gridStep])
    (StepDecomp_diag sz0 0) 0
    (stepDecomp_integrable_stepZ sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
      (StepDecomp_check_class sz0 0) (fun a A _ => Complex.ofReal_im _)
      (fun a M y _ _ => StepDecomp_check_hC₂ sz0 0 a M y) (by norm_num [gridStep])
      (StepDecomp_diag sz0 0) 0)

/-- `stepDecomp_Z_subG` at the same data, `E = univ`, `c = Δ · linTrVar 1`
(`c ≥ 0` by `linTrVar_nonneg`). -/
example :
    HasCondSubgaussianMGF (filt sz0 0) ((filt sz0).le 0)
      (fun ω => (Set.univ : Set (PathΩ sz0)).indicator (fun ω =>
        stepZ sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
          (StepDecomp_checkΦ sz0 0) (StepDecomp_diag sz0 0) 0 ω) ω)
      ⟨gridStep (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0
          * linTrVar 0 (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ),
        mul_nonneg (by norm_num [gridStep]) (linTrVar_nonneg 0 _)⟩ (pathP sz0) :=
  StepDecomp_check_Z_subG sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
    (by norm_num [gridStep]) 0

/-- `HermTestFun` and `gradMat` at `sz0`: the family `sin (Re tr)` is in the class, and its gradient
matrix at `M = 0` is `cos 0 • 1 = 1`, nonzero. -/
example : HermTestFun sz0 0 (StepDecomp_checkΦ sz0 0 0) := StepDecomp_check_class sz0 0 0

example :
    gradMat (StepDecomp_checkΦ sz0 0 0)
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
      = (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) := by
  have h : gradMat (StepDecomp_checkΦ sz0 0 0)
      (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
      = ((Real.cos (StepDecomp_g (Idx 3 (sz0.L 0) (sz0.W 0))
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) : ℝ) : ℂ)
        • (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) :=
    StepDecomp_check_gradMat _
  rw [h]
  simp [StepDecomp_g_apply]

/-- The moment bounds at `sz0`. -/
example : ∫ ω : PathΩ sz0, ‖Sizes.seqXmat sz0 0 (ω (0 + 1))‖ ^ 2 ∂(pathP sz0)
    ≤ 16 * (sz0.size 0 : ℝ) ^ 4 := integral_normSq_incr_le sz0 0 0

example : ∫ ω : PathΩ sz0, ‖Sizes.seqXmat sz0 0 (ω (0 + 1))‖ ^ 4 ∂(pathP sz0)
    ≤ 768 * (sz0.size 0 : ℝ) ^ 8 := integral_normPow4_incr_le sz0 0 0

end Instances
```

### b.6 Name-clash grep (public names of the file against the rest of RBM3D)
```
$ for n in <public names>; do grep -rnwE "(def|theorem|lemma|structure|abbrev|instance) (RBM\.Path\.)?$n" RBM3D --include="*.lean" | grep -v StepDecomp.lean | wc -l; done
gradMat: 0 fderiv_eq_trace_gradMat: 0 HermTestFun: 0 integrable_normSq_incr: 0 integrable_normPow4_incr: 0 integral_normSq_incr_le: 0 integral_normPow
4_incr_le: 0 Ab: 0 stepZ: 0 stepXi: 0 stepY: 0 lin_eq_fderiv: 0 stepDecomp: 0 stepDecomp_Y_sq: 0 stepDecomp_Z_subG: 0 stepDecomp_integrable_stepZ: 0 S
tepDecomp_check_stepDecomp: 0 StepDecomp_check_Z_subG: 0 StepDecomp_check_trace_not_hermTestFun: 0
```

### b.7 Port source (RBM2D, read-only, `git show c9a24cf:RBM2D/Path/StepDecomp.lean`, 1553 lines; HEAD of RBM2D is 9e0f275)
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/StepDecomp.lean
 RBM2D/Path/StepDecomp.lean | 415 ++++++++-------------------------------------
 1 file changed, 74 insertions(+), 341 deletions(-)
$ grep -cE "Z2|\(W \* L\) \^ 2|W \^ 2|pow_two|svar|gvar" <RBM2D c9a24cf file>
106
$ same grep on the new file, code lines only (docstring lines 17-60 excluded)
0
```

### b.8 Narrative
- Ported all of RBM2D `Path/StepDecomp.lean` at `c9a24cf` (1553 lines) into `RBM3D/Path/StepDecomp.lean` (1602 lines, namespace `RBM.Path`); no public declaration is dropped (the 19 public names are listed in b.6). Renaming R1-R4 of ST1-COMMON items 2-3: `d : Sizes` to `{d : ℕ} (sz : Sizes d)`, `Z2 (d.L n)` to `Zd d (sz.L n)`, `Idx` to `Idx d`, `Coord/P/gvar/svar` to `CoordF/PF/gvarF/svarF`, `Sizes.size d n` to `sz.size n`.
- Statement diff (b.4): `gradMat`, `HermTestFun`, `stepDecomp`, `stepDecomp_Z_subG`, `stepDecomp_Y_sq`, `stepDecomp_integrable_stepZ`, `integral_normSq_incr_le`, `integral_normPow4_incr_le` are identical to RBM2D's text after the renaming (script compares whitespace-normalised text). No other residual difference. `HermTestFun` takes `(sz : Sizes d) (n : ℕ)`, as the `(d : Sizes) (n : ℕ)` of RBM2D.
- Dimension-specific tokens (a, rows 1-9): lattice labels and `Idx` appear only as index types and in finite sums, no `d`-power in a statement. The only `N`-dependent quantities are `#CoordF = 2 N²` (`StepDecomp_card_Coord`, via `card_Idx`, `N = (W L)^d`) and the moment bounds `16 N⁴`, `768 N⁸`, which keep RBM2D's constants because only `#CoordF` and `gvarF ≤ 1` enter. After the renaming no `Z2`, `W^2`, `(W*L)^2`, `svar`, `gvar` token remains in code lines (b.7).
- The one proof that changed is `StepDecomp_gvar_le_one`: RBM2D bounds the fixed five-point profile; here `svarF = W^{-d} · SBR`, and `sbKernelR x ≤ Σ_x sbKernelR = 1` (`sum_sbKernelR`, needs `3 ≤ L`), `W^{-d} ≤ 1`, `gvarF ≤ svarF`. It adds a hypothesis `hL : 3 ≤ L` to `StepDecomp_gvar_le_one` and to the three private lemmas that use it (`StepDecomp_integral_pow4_coord_le`, `StepDecomp_integral_normSq_le`, `StepDecomp_integral_normPow4_le`), discharged by `Sizes.three_le_L` at the public moment theorems. This differs from the route written in (a) row 5 (`max(a,b) ≤ 1`), same conclusion; (a) is not wrong, so there is no (a′).
- `d`-dimensional sub-Gaussian constant of `stepDecomp_Z_subG`: it is the input `c ≥ Δ · linTrVar n (Ab ω)` on `E`; `linTrVar` is built from `Sizes.seqGvar`. For `A = 1` the value is `L^d/(1 + 2 d g²)` with `g = sz.lam n` (not `W`-dependent), checked numerically at `d = 3, L = 3, W = 2, g = 1/2` in (a) (10.8); it is not proved in Lean here (the statement does not need it).
- DECISIONS §29 boundary checks: no target has a time-window hypothesis other than `hΔ : 0 ≤ gridStep s t K n` (`stepDecomp`) and none for `stepDecomp_Z_subG`; `s`, `t`, `K` are free; no `∀ᶠ n`; the four items of (a) hold.
- Instances (b.5): `stepDecomp`, `stepDecomp_Z_subG`, `HermTestFun`, `gradMat` and both moment bounds are applied at the merged `sz0` (`d = 3`, `L 0 = 4`, `W 0 = 32`), `Φ_a = sin ∘ Re tr`, `U = 1` on the diagonal, `C₂ = ‖Re tr‖²`, `s = 1/4`, `t = 3/4`, `K = 2`, `j = 0`, `b = 0`; every hypothesis is discharged (no hypothesis of the examples remains open). The check lemmas `StepDecomp_check_*` are RBM2D's, retyped to `sz`; `A ↦ Re tr A` is shown not in the class (`StepDecomp_check_trace_not_hermTestFun`).
- Registry (DECISIONS §20): `Test/Axioms.lean` gets one line, `RBM.Path.HermTestFun` in `structuralProps` (a `Prop` structure on the data `Φ`, a hypothesis of `stepDecomp`, proved by no public theorem); the pre-check (b.2) exits 0 and the full `lake build` succeeds.
- Port source: RBM2D HEAD is `9e0f275`, not `c9a24cf`; the file differs between them (b.7). The port is taken from `git show c9a24cf:...`, as the ticket says.

## (c) Verified Mathlib names (compiled in this file)
`Finset.single_le_sum`, `inv_le_one_of_one_le₀` (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:945`), `one_le_pow₀`, `Fintype.card_bool`, `Fintype.card_prod`, `norm_image_sub_le_of_norm_deriv_right_le_segment` (`Analysis/Calculus/MeanValue.lean:308`), `image_norm_le_of_norm_deriv_right_le_deriv_boundary` (`MeanValue.lean:280`), `ConvexOn.map_condExp_le_univ`, `norm_condExp_le` (`CondJensen.lean:246`), `ContinuousLinearMap.comp_condExp_comm`; RBM3D: `sum_sbKernelR`, `sbKernelR_nonneg`, `SBR`, `card_Idx`, `svarF_nonneg`, `Sizes.three_le_L`, `Sizes.seqP_map_slice`, `map_incr`, `pathH_measurable_filt`, `pathH_isHermitian`, `condExp_linear_eq_zero`, `hasCondSubgaussianMGF_linear`, `linTrVar_nonneg`. No Mathlib name was found absent.

## (d) Open issues and paper-delta candidates
- T2073a (Lean-only, inherited from RBM2D T2076a): the observables enter `stepDecomp` through the class `HermTestFun` (`C²` and bounded at Hermitian points) plus the hypothesis `hC₂` on `fderiv²` along Hermitian directions; the paper's Taylor expansion of a resolvent polynomial states no such class. Not checked against the paper TeX in this ticket.
- T2073b: the moment bounds `E‖X‖² ≤ 16 N⁴`, `E‖X‖⁴ ≤ 768 N⁸` are crude polynomial bounds used only for integrability of the remainder; they are not statements of the paper.
- Open: `linTrVar n 1 = L^d/(1 + 2 d g²)` is not proved in Lean; consumers that need a numerical `c` (ST2-23, ST2-24, ST-3) must prove it or bound `linTrVar` directly.
