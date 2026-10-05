Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 05:54:55 UTC 2026

Evidence script (Python, scratchpad only, no Lean): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2177/pf.py`.
Sources read: ticket; `RBM3D/Universality/Pins.lean` (`ouP`, `ouMat`, `UNModel`, `UNModel.band`); `RBM3D/Gauss/FineModel.lean` (`gvarF`, `PF`, `seqGvar`, `seqP`, `slice`, `seqXmat`); `RBM3D/Defs/Block.lean:74` (`sbKernelR`); RBM2D `Universality/OU.lean`, `EigenMeasurable.lean` at `c9a24cf`.

### (i) Exponent table

There is no exponent in these targets; the constants are the OU weights, the variances and the Weyl constant.

| Constant / condition | Value | Constraint | Slack |
|---|---|---|---|
| OU weights in `ouMat` (`Pins.lean:150`) | `a = e^{-t/2}`, `b = sqrt(1-e^{-t})` | `a^2 + b^2 = 1` | equality, all `t` |
| `b` real | `1 - e^{-t} >= 0` iff `t >= 0` | `ouSample_law` needs hypothesis `0 <= t` (source `OU.lean:105`: `ht : 0 <= t`) | `t = 0`: `b = 0`; `t = 1/2, 2`: `b^2 = 0.3935, 0.8647` |
| `N` | `(W L)^d` (`Sizes.size`, `Defs/Sizes.lean:157`) | `L >= 3`, `W >= 1` | `d=3, L=3, W=1`: `N = 27`; `sz0`, `n=0`: `N = 2097152` |
| GUE coordinate variance `gueVar` | `1/N` diag, `1/(2N)` per real off-diag coordinate | `E\|h'_ij\|^2 = 1/N` | exact |
| band coordinate variance `gvarF d L W g` (`FineModel.lean:89`) | `S_ii` diag, `S_ij/2` off-diag, `S_xy = W^{-d} SBR(x-y)`, `SBR(0) = (1+2dg^2)^{-1}`, `SBR(x) = g^2 (1+2dg^2)^{-1}` if `\|x\|_1 = 1` | row sum of `S` is 1 (needs `L >= 3` so the `2d` neighbours are distinct) | script: row sums of `S` in `[0.9999999999999999, 1.0]` |
| OU coordinate variance `ouVar t c` | `e^{-t} gvarF(c) + (1-e^{-t}) gueVar(c)` (coupling `g = sz.lam n`, absent in RBM2D) | = law variance in `ouSample_law`; `t=0`: `ouVar = gvarF`; `t -> inf`: `gueVar` | row sum of `E\|h\|^2` is exactly 1 for every `t` |
| Two-Gaussian sum | `a X + b Y`, `X ~ N(0,v1)`, `Y ~ N(0,v2)` independent | law `N(0, a^2 v1 + b^2 v2)` | exact (no constant) |
| Weyl constant (`eigenvalues₀_abs_sub_le`, source `EigenMeasurable.lean:258`) | `\|λ_i(A)-λ_i(B)\| <= sqrt(Σ_{ab} \|(A-B)_{ab}\|^2)` | Hermitian `A, B`; dimension-free (index `n` is a generic finite type) | constant `1` |
| Measurability endpoint hypotheses | `Hm` measurable and everywhere Hermitian, `O` **continuous**, `k`, `c`, `E` arbitrary reals | the pin `IsTestFun` (`ContDiff`) implies `Continuous`, so a downstream test function discharges `hO` | `k = 2` needs `card ι >= 2` for a nonempty sum over `Fin 2 ↪ ι` |

Two statement-shape facts (no change of mathematics, but not a pure token replacement):
1. In RBM2D, `ouP L W` lives on `Ω L W × Ω L W` and `ouSample : Ω×Ω → Ω`. Here `ouP M n` (`Pins.lean:145`) lives on `SeqΩ sz × Ω d (L n) (W n)` for an abstract `M`. The law of the OU coordinates is a Gaussian law only if `M.μ` is Gaussian, so `ouSample_law` can hold only for `M = UNModel.band sz`, with `ouSample` built from `slice sz n ω.1` (`FineModel.lean:176`) and `ouVar` using `gvarF d (L n) (W n) (sz.lam n)`. The reduction is: `seqP` pushed by `slice` is `PF d (L n) (W n) (sz.lam n)` (`FineModel.lean:184`), so `(ouP (band sz) n).map (slice × id) = PF.prod gueP` and the source proof applies with `P → PF`.
2. `ouMat_zero_map`, `measurable_ouMat`, `measurable_ouSample` and the measurability targets hold for an abstract `M` (they use only `M.meas`, `M.herm`, `M.prob`). The source's `seqXmat_map_eq_ouMat_zero` is the band specialisation of `ouMat_zero_map` (`(band sz).H = seqXmat sz` by `UNModel.band`).
`EigenMeasurable` has no `d`: its generic statements are over `ι` with `Fintype`, `DecidableEq`; only its example section uses `Idx 3 3`, `ouMat 3 3 1`, which has to be re-based on `UNModel.band sz0` / the `Fin 3` matrices.

### (ii) Concrete nondegenerate instance

OU marginal at `d = 3`, `L = 3`, `W = 1` (`N = 27`, `g = 1/64 = sz0.lam 0`), `t ∈ {0, 1/2, 2}`; Monte Carlo `m = 20000` Hermitian samples of `H` (band profile) and `G` (GUE), `ouMat = a H + b G`. Then `sz0`, `n = 0` (`L=4, W=32`, `N = 128^3`) from the closed formulas; then the `k = 2` measurability data `H(w) = [[1,w,0],[w,2,0],[0,0,3]]` on `ι = Fin 3`, `Ω = ℝ`, `O = exp(-x0^2-x1^2)` (continuous), `E = 0`.

Command: `python3 .../T2177/pf.py`. Output (verbatim, the stderr RuntimeWarning, a `0/0` behind the `nan` of the `t=0` row, is omitted):

```
d,L,W,N,g = 3 3 1 27 0.015625  row sums of S (min,max): 0.9999999999999999 1.0  symmetric: True
t=0: a^2=1.000000=e^-t, b^2=0.000000; max|E|h|^2-(e^-t S+(1-e^-t)/N)|=0.00e+00; row sums of E|h|^2 in [1.000000000000,1.000000000000]; herm err=0.0e+00; MC (0,1) E|h|^2=0.00024 vs 0.00024; MC diag(0,0)=0.98685 vs 0.99854; MC max rel dev over all entries=nan
   t=0: ouVar==gvar: True
   Re h_01: var 0.00012094904213926545 vs 0.00012189176011701609  kurtosis 3.0086174461332122
t=0.5: a^2=0.606531=e^-t, b^2=0.393469; max|E|h|^2-(e^-t S+(1-e^-t)/N)|=1.73e-18; row sums of E|h|^2 in [1.000000000000,1.000000000000]; herm err=0.0e+00; MC (0,1) E|h|^2=0.01452 vs 0.01472; MC diag(0,0)=0.61388 vs 0.62022; MC max rel dev over all entries=0.028
   Re h_01: var 0.007258093298113753 vs 0.007360400354258169  kurtosis 3.017089811776731
t=2: a^2=0.135335=e^-t, b^2=0.864665; max|E|h|^2-(e^-t S+(1-e^-t)/N)|=0.00e+00; row sums of E|h|^2 in [1.000000000000,1.000000000000]; herm err=0.0e+00; MC (0,1) E|h|^2=0.03163 vs 0.03206; MC diag(0,0)=0.16616 vs 0.16716; MC max rel dev over all entries=0.025
   Re h_01: var 0.01584879912946212 vs 0.016028805825572003  kurtosis 3.0170965202637894
sz0 n=0: N= 2097152 S_xx= 3.047294002925402e-05 S block row-sum= 1.0 1/N= 4.76837158203125e-07
  t=0 ouVar diag = 3.047294e-05, rowsum E|h|^2 = 1.000000000000
  t=0.5 ouVar diag = 1.867039e-05, rowsum E|h|^2 = 1.000000000000
  t=2 ouVar diag = 4.536368e-06, rowsum E|h|^2 = 1.000000000000
kPoint k=2 at w=0,0.1,0.5,1: [8.587555741648182e-20, 7.17292949983251e-20, 9.539912700593316e-22, 1.3078830053769379e-27]  #embeddings Fin2->Fin3 = 6
```

Reading of the output: `max|E|h|^2 - (e^{-t} S + (1-e^{-t})/N)|` is at most `1.73e-18`, so the variance profile of `ouMat M n t` for the band model is `e^{-t} S_ij + (1-e^{-t})/N`, as in the docstring of RBM2D `OU.lean:46` (`1-2:334-337` of the RBM2D paper). `ouVar = gvarF` at `t = 0`. The Hermitian error is `0.0`. The sample variance of `Re h_01` matches `ouVar` within `1.5%` and its kurtosis is `3.01-3.02` (Gaussian). All hypotheses hold at once: `0 <= t`, `L >= 3`, `W >= 1`, `N > 1`, the matrices are Hermitian, the dimension `3` makes `Fin 2 ↪ Fin 3` have `6` elements (nonempty sum, no `N = 0`, no collapsed window), and `kPoint` values (`~1e-20..1e-27`) are positive and vary with `w` (nonconstant, although small at `E = 0`, `N = 3`; any real `E` is allowed by the statement).

External hypothesis: none. `ouSample_law`, `ouMat_zero_map`, `measurable_corrSum`, `measurable_kPoint_eigenvalues` use no `UNL32`-type input (no borrowed pin).

### Verdict per target

- `ouSample_law`: PASS, with the shape in note 1 (statement for `UNModel.band sz`, not for abstract `M`; the prover must state it that way and propose a paper-delta candidate for the difference from the RBM2D form).
- `ouMat_zero_map`: PASS (abstract `M`; `(ouP M n).map (ouMat M n 0) = M.μ.map (M.H n)` by `ouMat_zero`, `Measure.map_fst_prod`, `measure_univ`).
- `measurable_corrSum`: PASS (generic `ι`, `hO : Continuous O`).
- `measurable_kPoint_eigenvalues`: PASS (same hypotheses; instance at `k = 2`, `ι = Fin 3`).

## (b) Script output -- Mon Oct  5 05:59:20 UTC 2026

Branch `t/T2177`, commit `dc24260` (files: `RBM3D/Universality/OU.lean`      312 lines, `RBM3D/Universality/EigenMeasurable.lean`      597 lines).

$ git diff --stat main...t/T2177
 RBM3D/Universality/EigenMeasurable.lean | 597 ++++++++++++++++++++++++++++++++
 RBM3D/Universality/OU.lean              | 312 +++++++++++++++++
 2 files changed, 909 insertions(+)

$ lake build   (whole library, in the worktree)
Build completed successfully (3961 jobs).

### Build, axioms, hygiene, name clashes
```
$ lake build RBM3D.Universality.OU RBM3D.Universality.EigenMeasurable 2>&1 | grep -v "linter\|^$" | tail -4
RBM3D/Universality/OU.lean:302:0: 'RBM.Univ.isProbabilityMeasure_ouP' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/OU.lean:303:0: 'RBM.Univ.ouMat_eq_Xmat_ouSample' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/OU.lean:304:0: 'RBM.Univ.measurable_ouSample' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/OU.lean:305:0: 'RBM.Univ.measurable_ouMat' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/OU.lean:306:0: 'RBM.Univ.ouSample_law' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/OU.lean:307:0: 'RBM.Univ.ouMat_zero_map' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/OU.lean:308:0: 'RBM.Univ.seqXmat_map_eq_ouMat_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/EigenMeasurable.lean:589:0: 'RBM.Univ.eigenvalues₀_abs_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/EigenMeasurable.lean:590:0: 'RBM.Univ.measurable_corrSum' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/EigenMeasurable.lean:591:0: 'RBM.Univ.measurable_kPoint_eigenvalues' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/EigenMeasurable.lean:592:0: 'RBM.Univ.integral_kPoint_eq_of_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/EigenMeasurable.lean:593:0: 'RBM.Univ.EigenMeasurableCheck.measurable_Hw' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/EigenMeasurable.lean:594:0: 'RBM.Univ.EigenMeasurableCheck.T3aStmt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Universality/EigenMeasurable.lean:595:0: 'RBM.Univ.EigenMeasurableCheck.T3bStmt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3331 jobs).

$ grep -c sorry/admit/native_decide/axiom
RBM3D/Universality/OU.lean:0
RBM3D/Universality/EigenMeasurable.lean:0
$ name-clash grep (public names, whole RBM3D excluding the two new files)
isProbabilityMeasure_ouP:        0
ouSample:        0
ouVar:        0
ouMat_eq_Xmat_ouSample:        0
measurable_ouSample:        0
measurable_ouMat:        0
ouSample_law:        0
ouMat_zero_map:        0
seqXmat_map_eq_ouMat_zero:        0
eigenvalues₀_abs_sub_le:        0
measurable_corrSum:        0
measurable_kPoint_eigenvalues:        0
integral_kPoint_eq_of_map_eq:        0
```

### Target statements (extracted by script) and RBM2D sources at c9a24cf
```
--- RBM3D OU.lean: ouSample_law
theorem ouSample_law (sz : Sizes d) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (ouP (UNModel.band sz) n).map (ouSample sz n t) =
      Measure.infinitePi (fun c => gaussianReal 0 (ouVar d (sz.L n) (sz.W n) (sz.lam n) t c)) := by
--- RBM2D OU.lean @c9a24cf: ouSample_law
theorem ouSample_law {t : ℝ} (ht : 0 ≤ t) :
    (ouP L W).map (ouSample L W t) =
      Measure.infinitePi (fun c => gaussianReal 0 (ouVar L W t c)) := by
--- RBM3D OU.lean: ouMat_zero_map
theorem ouMat_zero_map (M : UNModel sz) (n : ℕ) :
    (ouP M n).map (ouMat M n 0) = M.μ.map (M.H n) := by
--- RBM2D OU.lean @c9a24cf: ouMat_zero_map
theorem ouMat_zero_map :
    (ouP L W).map (ouMat L W 0) = (P L W).map (Xmat L W) := by
--- RBM3D OU.lean: seqXmat_map_eq_ouMat_zero
theorem seqXmat_map_eq_ouMat_zero (sz : Sizes d) (n : ℕ) :
    (seqP sz).map (seqXmat sz n) = (ouP (UNModel.band sz) n).map (ouMat (UNModel.band sz) n 0) :=
--- RBM2D OU.lean @c9a24cf: seqXmat_map_eq_ouMat_zero
theorem seqXmat_map_eq_ouMat_zero (d : Sizes) (n : ℕ) :
    (seqP d).map (seqXmat d n) = (ouP (d.L n) (d.W n)).map (ouMat (d.L n) (d.W n) 0) := by
--- RBM3D EigenMeasurable.lean: eigenvalues₀_abs_sub_le
theorem eigenvalues₀_abs_sub_le {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ Real.sqrt (∑ a, ∑ b, ‖(A - B) a b‖ ^ 2) := by
--- RBM3D EigenMeasurable.lean: measurable_corrSum
theorem measurable_corrSum {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*} [Fintype n]
    [DecidableEq n] {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : Continuous O)
    (c E : ℝ) :
    Measurable (fun ω => ∑ f : Fin k ↪ n, O (fun j => c * ((hH ω).eigenvalues (f j) - E))) := by
--- RBM3D EigenMeasurable.lean: measurable_kPoint_eigenvalues
theorem measurable_kPoint_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] (H : Ω → Matrix ι ι ℂ) (hH : ∀ ω, (H ω).IsHermitian)
    (hmeas : Measurable H) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (hO : Continuous O) (E : ℝ) :
    Measurable (fun ω => kPoint k O E (hH ω).eigenvalues) := by
--- RBM3D EigenMeasurable.lean: integral_kPoint_eq_of_map_eq
theorem integral_kPoint_eq_of_map_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁)
    (P₂ : Measure Ω₂) (H₁ : Ω₁ → Matrix ι ι ℂ) (H₂ : Ω₂ → Matrix ι ι ℂ)
    (hH₁ : ∀ ω, (H₁ ω).IsHermitian) (hH₂ : ∀ ω, (H₂ ω).IsHermitian)
    (hmeas₁ : Measurable H₁) (hmeas₂ : Measurable H₂) (hlaw : P₁.map H₁ = P₂.map H₂)
    (k : ℕ) (O : (Fin k → ℝ) → ℝ) (hO : Continuous O) (E : ℝ) :
    ∫ ω, kPoint k O E (hH₁ ω).eigenvalues ∂P₁ = ∫ ω, kPoint k O E (hH₂ ω).eigenvalues ∂P₂ := by
```

### Compiled nonempty instances (extracted by script from the files)
```
-- OU.lean (lines 260-299), UNModel.band sz0, n = 0 (d = 3, L = 4, W = 32, lam = 1/64, N = 2097152)

/-- `ouSample_law` at `UNModel.band sz0`, `n = 0`, `t = 1`. -/
example : (ouP (UNModel.band sz0) 0).map (ouSample sz0 0 1) =
    Measure.infinitePi (fun c => gaussianReal 0 (ouVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 1 c)) :=
  ouSample_law sz0 0 zero_le_one

/-- `ouSample_law` at `t = 1/2` and `t = 0` (the limit `t = 0` has `ouVar = gvarF`). -/
example : (ouP (UNModel.band sz0) 0).map (ouSample sz0 0 (1 / 2)) =
    Measure.infinitePi (fun c => gaussianReal 0
      (ouVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 2) c)) :=
  ouSample_law sz0 0 (by norm_num)

example : (ouP (UNModel.band sz0) 0).map (ouSample sz0 0 0) =
    Measure.infinitePi (fun c => gaussianReal 0
      (ouVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 c)) :=
  ouSample_law sz0 0 le_rfl

/-- At `t = 0` the OU variance is the band variance (`ouVar = gvarF`). -/
theorem ouVar_zero (c : CoordF 3 (sz0.L 0) (sz0.W 0)) :
    ouVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 c = gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c := by
  simp [ouVar]

/-- At `t = 1` the weights `e^{-1}`, `1 - e^{-1}` are both positive: the GUE part is nonzero. -/
theorem ouVar_one_gue_weight_pos : 0 < (1 - Real.exp (-1)).toNNReal := by
  rw [Real.toNNReal_pos, sub_pos]
  exact Real.exp_lt_one_iff.2 (by norm_num)

/-- `ouMat_zero_map` at `UNModel.band sz0`, `n = 0`. -/
example : (ouP (UNModel.band sz0) 0).map (ouMat (UNModel.band sz0) 0 0) =
    (UNModel.band sz0).μ.map ((UNModel.band sz0).H 0) :=
  ouMat_zero_map (UNModel.band sz0) 0

example : (seqP sz0).map (seqXmat sz0 0) =
    (ouP (UNModel.band sz0) 0).map (ouMat (UNModel.band sz0) 0 0) :=
  seqXmat_map_eq_ouMat_zero sz0 0

-- (measurable_ouMat, measurable_ouSample, ouMat_eq_Xmat_ouSample instances: file lines 296-300, omitted here)

-- EigenMeasurable.lean (lines 526-565), k = 2
/-- `measurable_corrSum` at `H = Hw` on `Ω = ℝ`, `k = 2`, `ι = Fin 3` (`Fin 2 ↪ Fin 3` has 6 elements). -/
example : Measurable (fun w : ℝ => ∑ f : Fin 2 ↪ Fin 3,
    (fun x : Fin 2 → ℝ => Real.exp (-(x 0) ^ 2 - (x 1) ^ 2))
      (fun j => (Fintype.card (Fin 3) : ℝ) * ((Hw_herm w).eigenvalues (f j) - 0))) :=
  measurable_corrSum measurable_Hw Hw_herm 2 O2_cont (Fintype.card (Fin 3) : ℝ) 0

/-- `measurable_kPoint_eigenvalues` at `H = Hw`, `k = 2`, `E = 0`. -/
example : Measurable (fun w : ℝ => kPoint 2 (fun x : Fin 2 → ℝ => Real.exp (-(x 0) ^ 2 - (x 1) ^ 2)) 0
    (Hw_herm w).eigenvalues) :=
  measurable_kPoint_eigenvalues Hw Hw_herm measurable_Hw 2 _ O2_cont 0

-- (measurable_corrSum at the OU marginal of UNModel.band sz0: file lines 537-545, omitted)
/-- `measurable_kPoint_eigenvalues` at `𝐇_1` of `UNModel.band sz0`, `n = 0`, `k = 2`, `E = 0`. -/
example : Measurable (fun ω => kPoint 2 (fun x : Fin 2 → ℝ => Real.exp (-(x 0) ^ 2 - (x 1) ^ 2)) 0
    (ouMat_isHermitian (UNModel.band sz0) 0 1 ω).eigenvalues) :=
  measurable_kPoint_eigenvalues (ouMat (UNModel.band sz0) 0 1) (ouMat_isHermitian (UNModel.band sz0) 0 1)
    (measurable_ouMat (UNModel.band sz0) 0 1) 2 _ O2_cont 0

-- (private measurable_Hband : Measurable ((UNModel.band sz0).H 0), file line 553)
/-- `integral_kPoint_eq_of_map_eq` for `H₁ = 𝐇_0` on `ouP` and `H₂ = H` on `μ` (`ouMat_zero_map`). -/
example : ∫ ω, kPoint 2 (fun x : Fin 2 → ℝ => Real.exp (-(x 0) ^ 2 - (x 1) ^ 2)) 0
      (ouMat_isHermitian (UNModel.band sz0) 0 0 ω).eigenvalues ∂(ouP (UNModel.band sz0) 0) =
    ∫ ω, kPoint 2 (fun x : Fin 2 → ℝ => Real.exp (-(x 0) ^ 2 - (x 1) ^ 2)) 0
      ((UNModel.band sz0).herm 0 ω).eigenvalues ∂(UNModel.band sz0).μ :=
  integral_kPoint_eq_of_map_eq (ouP (UNModel.band sz0) 0) (UNModel.band sz0).μ
    (ouMat (UNModel.band sz0) 0 0) ((UNModel.band sz0).H 0)
    (ouMat_isHermitian (UNModel.band sz0) 0 0) ((UNModel.band sz0).herm 0)
    (measurable_ouMat (UNModel.band sz0) 0 0) measurable_Hband
    (ouMat_zero_map (UNModel.band sz0) 0) 2 _ O2_cont 0
```

### Port citations (CLAUDE.md 5.2)
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/OU.lean RBM2D/Universality/EigenMeasurable.lean
 RBM2D/Universality/EigenMeasurable.lean | 139 ++++----------------------------
 RBM2D/Universality/OU.lean              | 129 +++--------------------------
 2 files changed, 26 insertions(+), 242 deletions(-)
$ diff <(RBM2D EigenMeasurable.lean:30-482) <(RBM3D EigenMeasurable.lean:30-500, the ported body)
1d0
< noncomputable section
256d254
< open RBM.Endpoints
257a256
> 
453a453,471
> 
> /-! ### Compiled nonempty instances -/
> 
> namespace EigenMeasurableCheck
> 
```

### Narrative (b)

- Both files are in the branch; `lake build` of each module and of the whole library succeeded; the
  seven new public declarations of `OU.lean` and the four of `EigenMeasurable.lean` print only the
  three standard axioms; no `sorry`/`admit`/`native_decide`/`axiom`.
- `EigenMeasurable.lean`: the RBM2D body (lines 30-482 of the source) is copied verbatim except the
  line `open RBM.Endpoints` (not needed: `kPoint` is `RBM.Univ.kPoint`); the diff above shows that
  line, the `noncomputable section` line (kept before the namespace), a blank line, and the appended
  instance section. The statements are generic in the finite index type `ι`, so no `d`-dependent
  token occurs. Only the instances are new (k = 2, `Fin 3` and the band model `UNModel.band sz0`).
- `OU.lean`: the proof of `ouSample_law` is the RBM2D proof, stated on the pair space as the private
  `ouSamplePair_law` (`PF d L W g` replaces `P L W`), then transferred to `ouP (UNModel.band sz) n` by
  `Measure.map_prod_map`, `seqP_map_slice`. Preflight note 1 is followed: the law is stated for the band
  model only; the source's `ou_measurable_Xmat` is not needed, since `measurable_ouMat` is proved entrywise
  for an abstract `UNModel` (`M.meas`, `measurable_Xentry`).
- Declarations that `Pins.lean` already holds (`ouP`, `ouMat`, `ouMat_isHermitian`, `ouMat_zero`,
  `isProbabilityMeasure_gueP`) are used, not re-declared. `isProbabilityMeasure_ouP` is new (absent in
  `Pins.lean`), for an abstract `M`.
- Public RBM2D names kept: `ouSample`, `ouVar`, `ouMat_eq_Xmat_ouSample`, `measurable_ouSample`,
  `measurable_ouMat`, `ouSample_law`, `ouMat_zero_map`, `seqXmat_map_eq_ouMat_zero`,
  `isProbabilityMeasure_ouP`, `eigenvalues₀_abs_sub_le`, `measurable_corrSum`,
  `measurable_kPoint_eigenvalues`, `integral_kPoint_eq_of_map_eq`. `isProbabilityMeasure_gueP`
  (source `OU.lean`) already lives in `Pins.lean:70`. The RBM2D `OUCheck` examples at `L = W = 3`
  are not ported verbatim; `OUCheck.ouVar_zero`, `OUCheck.ouVar_one_gue_weight_pos` are new.
- The RBM2D head moved since `c9a24cf` (diff stat above); the port is against `c9a24cf`. No (a′) was needed.

## (c) Verified Mathlib names (each used and compiled in the two files)

`Measure.map_prod_map`, `Measure.map_id`, `Measure.map_fst_prod`, `Measure.infinitePi_map_restrict`,
`Measure.isProjectiveLimit_infinitePi`, `IsProjectiveLimit.unique`, `Measure.pi_map_pi`,
`measurePreserving_arrowProdEquivProdArrow`, `gaussianReal_map_const_mul`, `gaussianReal_conv_gaussianReal`,
`Matrix.toEuclideanLin`, `Matrix.cstar_norm_def`; module `Mathlib.Analysis.Matrix.MeasurableSpace` (gives
`MeasurableSpace (Matrix m n α)`; `OU.lean` imports it). `dif_pos` is deprecated here (warning, ported body).

## (d) Open issues and paper-delta candidates

- `T2177a` (shape, not mathematics): RBM2D `ouSample_law` is on `ouP L W` with `ouSample L W t`; here
  `ouSample sz n t` reads the model coordinate through `slice sz n`, `ouVar` has the extra argument
  `g = sz.lam n`, and the statement is for `UNModel.band sz` (the Gaussian law holds only for the Gaussian
  band model; an abstract `M` has no Gaussian law). The RBM2D identity `ouMat = Xmat ∘ ouSample` is
  `ouMat_eq_Xmat_ouSample` for `UNModel.band sz` only.
- `T2177b`: RBM2D `ouMat_zero_map` reads `(P L W).map (Xmat L W)`; here it is `M.μ.map (M.H n)` for every
  `UNModel M`; the band instance is `seqXmat_map_eq_ouMat_zero` (`seqP sz` / `seqXmat sz n`).
- `T2177c`: `measurable_ouMat` now takes `M : UNModel sz` and `n`; `ouSample`, `ouMat_eq_Xmat_ouSample`,
  `measurable_ouSample`, `seqXmat_map_eq_ouMat_zero` take `sz : Sizes d` explicitly (RBM2D: `L W` / `d : Sizes`).
- No external hypothesis; no change to `Pins.lean`.
