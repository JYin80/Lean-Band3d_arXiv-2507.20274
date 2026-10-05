Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 06:59:08 UTC 2026

### (i) Exponent table

Setting: `d = 3`, `L = 3`, `W = 1`, `N = (W L)^d = 27`, `k = 1`. No exponent of the paper enters this file (pure port; `gueVar` of `Pins.lean:61` is `1/N` on the diagonal, `1/(2N)` per real off-diagonal coordinate).

| quantity | value | constraint | slack |
|---|---|---|---|
| OU weights `a² = e^{-t}`, `b² = 1-e^{-t}` | `t=0`: 1, 0; `t=1/2`: 0.606531, 0.393469; `t=2`: 0.135335, 0.864665 | `t ≥ 0` (`b = √(1-e^{-t})` real), `a²+b² = 1` | `a²+b²-1 = 0` (float err ≤ 1.1e-16) |
| entry variance of `e^{-t/2}G + b G'` (diag / off-diag coordinate) | `1/27 = 0.0370370` / `1/54 = 0.0185185` for all three `t` | `= gueVar` exactly (`a² v + b² v = v`) | err 0.0 (all `t`) |
| Lipschitz window `ρ ∈ [ρmin, ρmax]` | `[1/2, 2]` | `0 < ρmin ≤ ρmax` (hyps `h0`, `h1`) | `ρmin = 1/2 > 0`; `ρmax - ρmin = 3/2` |
| test function `O` (k=1): `R0` (support radius), `B0 = sup|O|`, `B1 = sup‖DO‖` | `2`, `1`, `2` for the profile `smoothTransition(2-|x|)` (`rIn=1`, `rOut=2`) | `O` is `C^∞`, compact support (`IsTestFun`) | `B0,B1 < ∞` by compactness |
| `R1 = R0/ρmin` (radius where `Q ≡ 1`) | `4` | `Q` bump `=1` on `‖x‖ ≤ R1` | source bump: `rIn = max R1 0 + 1 = 5`, `rOut = 6` (script uses a bump `=1` on `‖x‖ ≤ 4`, support radius 5: any such `Q` works) |
| Lipschitz constant `C = k ρmax^{k-1} B0 + ρmax^k B1 R1` (source `Step1Cond_pointwise_lipschitz`, source `:371`) | `1·2⁰·1 + 2·2·4 = 17` | `C ≥ 0`; depends only on `k, O, ρmin, ρmax`, not on `N`, `Pm`, `E` | grid check below: worst `lhs - C|ρ-ρ'|Q = 0` |
| counting prefactor `N^k/N.descFactorial k` | `27/27 = 1` (k=1) | `≤ (N/(N-k))^k` (source `Step1Cond_prefactor_le`), needs `k < N` | `(27/26)^1 = 1.038462`, slack `0.0385` |
| counting hypothesis `k < Fintype.card n` | `1 < 27` | `k < N` | `26` |
| box constants `B`, `R` (`Step1Cond_exists_le_indicator`) | `B = B0+1 = 2`, `R = R0 = 2` | `0 < B`, `0 ≤ R`, `Q ≤ B·1_{[-R,R]^k}` | `B - B0 = 1` |
| counting window `R/N` | `2/27` | `|λ_i - E| ≤ R/N` | — |
| dominating test function (`ρ ∈ [ρmin,ρmax]`, `Q β ≤ Q'(ρβ)`) | `Q' = B0·b`, `b ≡ 1` on `‖y‖ ≤ ρbar·R0`, `ρbar = max|ρmin| |ρmax| = 2` → radius `4` | no sign condition on `ρmin,ρmax` | `‖ρβ‖ ≤ 2·2 = 4` for `‖β‖ ≤ R0` |

Constants of `Step1Cond_scaledPairing_lipschitz`: `Q` = bump `=1` on `‖x‖ ≤ R0/ρmin`, `C = k ρmax^{k-1} B0 + ρmax^k B1 R0/ρmin` (functions of `k`, `ρmin`, `ρmax`, `O`; no `N`). Of `Step1Cond_corrPairing_le_count`: constant `(N/(N-k))^k`, `k < N`; `_smul` version: `B (N/(N-k))^k`.

### (ii) One concrete nondegenerate instance

`d=3, L=3, W=1, N=27, k=1, t ∈ {0,1/2,2}, E ∈ {-1,0,0.7}, ρ,ρ' ∈ [1/2,2]`, `O = Q`-profile bump. Every hypothesis of the eight targets holds: `0 ≤ t`; `O` continuous with compact support and `C^∞`; `μ = gueP 3 3 1` probability measure; `0 < ρmin ≤ ρmax`; `k = 1 < 27`; `0 ≤ Q`, `Q ≤ B·1_{[-R,R]}`, `0 < B`. Command and output (script `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2183/pf.py`: exact variances, 2000-sample empirical entry variances of the Hermitian `N×N` OU matrix, `B0`, `B1` by finite differences, a grid check of the pointwise Lipschitz inequality with `Q = smoothTransition(5-|x|)` for `|x|>4`, `1` else, and 900 `(GUE sample, E)` checks of the counting bound):
```
$ python3 .../T2183/pf.py
N = 27 diag var = 0.037037037037037035 offdiag real-coordinate var = 0.018518518518518517
t=0.0: a^2=1.000000 b^2=0.000000 a^2+b^2-1=0.0e+00; diag var 0.0370370370 (err 0.0e+00); offdiag var 0.0185185185 (err 0.0e+00)
t=0.5: a^2=0.606531 b^2=0.393469 a^2+b^2-1=0.0e+00; diag var 0.0370370370 (err 0.0e+00); offdiag var 0.0185185185 (err 0.0e+00)
t=2.0: a^2=0.135335 b^2=0.864665 a^2+b^2-1=-1.1e-16; diag var 0.0370370370 (err 0.0e+00); offdiag var 0.0185185185 (err 0.0e+00)
t=0.0: empirical E|h_01|^2=0.03864, E h_00^2=0.03668, 1/N=0.03704
t=0.5: empirical E|h_01|^2=0.03742, E h_00^2=0.03821, 1/N=0.03704
t=2.0: empirical E|h_01|^2=0.03708, E h_00^2=0.03706, 1/N=0.03704
B0=1.0000 B1=2.0000 R0=2.0 R1=4.0 C=k*rmax^(k-1)*B0+rmax^k*B1*R1=17.0000
max over grid of (lhs - C|rho-rho'|Q(x)) = 0 (<=0 required)
prefactor N^k/N.descFactorial k = 1.0 <= (N/(N-k))^k = 1.038462
max over 900 (sample,E) of (kPoint Q - B(N/(N-k))^k #count^k) = 0.0 (<=0 required)
```
(Lean's `bump` of `Fin 1 → ℝ` is `ContDiffBump`, built from a non-explicit base, so `B1 = 2` is for the explicit 1-D profile above; in Lean `B0, B1` are obtained by `bounded_above_of_compact_support`, not computed.) No external hypothesis is introduced by this file (`gueP_map_unitary_conj` `GUEInvariance.lean:1001`, `ouSample_law`, `integral_kPoint_eq_of_map_eq` are proved, merged); no limit computation applies.

### Finding for stage 1b (statement shape, not mathematics)

On `main`, `ouMat` is model-indexed: `ouMat (M : UNModel sz) n t : SeqΩ sz × Ω d (sz.L n) (sz.W n) → Matrix` `= e^{-t/2} • M.H n ω.1 + √(1-e^{-t}) • Xmat ω.2` (`RBM3D/Universality/Pins.lean:150`), `ouP M n = M.μ.prod (gueP ..)` (`:145`). RBM2D's `ouMat L W t` on `Ω L W × Ω L W` (`RBM2D/Universality/Pins.lean:56`, `ouP` `:50`) has no merged counterpart; `T1Stmt` of the source (`:757`) is not statable verbatim. The two ouMat-mentioning targets need this shape change; the inner proof (`Step1Cond_inner_eq`: spectral theorem for `M.H n x`, conjugation, `gueP_map_unitary_conj`) is unchanged because it only uses that the first block is a fixed Hermitian matrix. Math check: with `H₀ := M.H n ω₁` Hermitian, `Vᴴ(a H₀ + b X₂)V = a D + b VᴴX₂V`, law of `VᴴX₂V` = GUE.
* `integral_kPoint_ouMat_cond`: for `M : UNModel sz`, `n`: `∫ kPoint k O E (ouMat_isHermitian M n t ω).eigenvalues ∂(ouP M n) = ∫ ω₁, ∫ ω₂ kPoint k O E (dbmMat_isHermitian d _ _ (fun i => e^{-t/2} (M.herm n ω₁).eigenvalues i) (1-e^{-t}) ω₂).eigenvalues ∂gueP ∂M.μ` (same RHS as the source with `d`). Measurability from `M.meas`.
* `gueP_prod_map_ouMat`: no model has `μ = gueP` on a `SeqΩ`; state with the explicit matrix `fun ω => e^{-t/2} • Xmat ω.1 + √(1-e^{-t}) • Xmat ω.2` on `(gueP d L W).prod (gueP d L W)` (this is `ouMat` of RBM2D by definition), `= (gueP d L W).map (Xmat d L W)`, `0 ≤ t`. `Step1Cond_gueMatPairing_eq_integral` (statement has no `ouMat`) then follows as in the source, via the explicit-matrix form of the conditioning identity at `μ = gueP`; the conditioning lemma should therefore be proved for a general measurable Hermitian family `H₀ : Ω₀ → Matrix` on a probability space (then `ouMat M n t = ...` with `H₀ = M.H n` by `rfl`).
Both shapes are paper-delta candidates `T2183a` (shape of `ouMat`, not a mathematical difference). Instances at `d=3, L=3, W=1` need a `Sizes 3` with `L = 3`, `W = 1` (constant sequence: `three_le_L`, `W_pos` hold; `sz0` has `L 0 = 4, W 0 = 32` and is not usable for `N = 27`).

### Verdicts

* `gueP_prod_map_ouMat`: PASS (true: `a²+b²=1`; coordinates independent Gaussians of variance `v`; explicit-matrix shape, see finding).
* `integral_kPoint_ouMat_cond`: PASS (model-indexed or general-`H₀` shape, see finding).
* `Step1Cond_gueMatPairing_eq_integral`: PASS.
* `Step1Cond_scaledPairing_lipschitz`: PASS (`C = 17` at the instance; grid slack 0).
* `Step1Cond_exists_dominating_testFun`: PASS.
* `Step1Cond_corrPairing_le_count`: PASS (`k=1<27`; prefactor 1 ≤ 1.038462).
* `Step1Cond_exists_le_indicator`: PASS.
* `Step1Cond_corrPairing_le_count_smul`: PASS (`B = 2`).

## (b) Script output — Mon Oct  5 07:04:26 UTC 2026

### Build (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2183, branch t/T2183, commit 4f681fa)
```
$ lake build RBM3D.Universality.Step1Cond   (tail; lines after the Step1Cond line)
Build completed successfully (3348 jobs).
$ lake build   (full library, worktree)
Build completed successfully (3988 jobs).
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Universality.Step1Cond; #assert_rbm_axioms)
exit 0
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/Step1Cond.lean
(no matches, grep exit 1)
```

### Ported statements vs RBM2D `c9a24cf` (script; source text normalised only by `L W -> d L W`)
```
$ python3 cmp.py src.lean Step1Cond.lean   (the "d d" deletions are an artifact of the normalisation)
== gueP_prod_map_ouMat DIFFERS
   delete 'theorem gueP_prod_map_ouMat (d d L W : ℕ)' -> 'theorem gueP_prod_map_ouMat (d L W : ℕ)'
   replace ' L W).prod (gueP d L W)).map (ouMat d L W t) = (gueP d' -> ' L W).prod (gueP d L W)).map (fun ω : Ω d L W × Ω d L W => Real.e'
   replace ' d L W)).map (ouMat d L W t) = (gueP d L W).map (Xmat d L W' -> 'p (fun ω : Ω d L W × Ω d L W => Real.exp (-t / 2) • Xmat d L W'
   replace '= (gueP d L W).map (Xmat d L W)' -> 'Real.exp (-t / 2) • Xmat d L W ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω.2) = (gueP d L W).map (Xmat d L W)'
== integral_kPoint_ouMat_cond DIFFERS
   replace 'em integral_kPoint_ouMat_cond (d d L W : ℕ) [NeZ' -> 'em integral_kPoint_ouMat_cond {d : ℕ} {sz '
   replace 'kPoint_ouMat_cond (d d L W : ℕ) [NeZero L] ' -> 'egral_kPoint_ouMat_cond {d : ℕ} {sz : Sizes d} (M : UNModel sz)'
   replace 'nt_ouMat_cond (d d L W : ℕ) [NeZero L] [NeZero W] (μ : Measure (Ω d L W)) [IsProbabilityMeasure μ] (t : ℝ) (' -> '{d : ℕ} {sz : Sizes d} (M : UNModel sz) (n : ℕ) (t : ℝ) ('
   insert 'oint k O E (ouMat_isHermitian t ω).eigen' -> 'oint k O E (ouMat_isHermitian M n t ω).eigen'
   replace 'sHermitian t ω).eigenvalues ∂(μ.prod (gueP d L W)) ' -> 'mitian M n t ω).eigenvalues ∂(ouP M n) = ∫'
   replace 'ω).eigenvalues ∂(μ.prod (gueP d L W)) = ∫ ω₁, ' -> 'an M n t ω).eigenvalues ∂(ouP M n) = ∫ ω₁, '
   insert 't k O E (dbmMat_isHermitian d L W (fun i' -> 't k O E (dbmMat_isHermitian d (sz.L n) (sz.W'
   insert 'k O E (dbmMat_isHermitian d L W (fun i =' -> 'E (dbmMat_isHermitian d (sz.L n) (sz.W n) (fun '
   insert ' O E (dbmMat_isHermitian d L W (fun i =>' -> 't_isHermitian d (sz.L n) (sz.W n) (fun i =>'
   replace 'fun i => Real.exp (-t / 2) * (Xmat_isHermitian d L W ω₁).eigen' -> 'fun i => Real.exp (-t / 2) * (M.herm n ω₁).eigen'
   insert '-t)) ω₂).eigenvalues ∂(gueP d L W)) ∂μ' -> '-t)) ω₂).eigenvalues ∂(gueP d (sz.L n) (sz.W'
   insert ')) ω₂).eigenvalues ∂(gueP d L W)) ∂μ' -> '₂).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) ∂M.'
   insert ') ω₂).eigenvalues ∂(gueP d L W)) ∂μ' -> 'values ∂(gueP d (sz.L n) (sz.W n))) ∂M.μ'
   insert ').eigenvalues ∂(gueP d L W)) ∂μ' -> '∂(gueP d (sz.L n) (sz.W n))) ∂M.μ'
== Step1Cond_gueMatPairing_eq_integral DIFFERS
   delete '_gueMatPairing_eq_integral (d d L W : ℕ) [' -> '_gueMatPairing_eq_integral (d L W : ℕ) ['
== Step1Cond_scaledPairing_lipschitz IDENTICAL after d-replacement
== Step1Cond_exists_dominating_testFun IDENTICAL after d-replacement
== Step1Cond_corrPairing_le_count IDENTICAL after d-replacement
== Step1Cond_exists_le_indicator IDENTICAL after d-replacement
== Step1Cond_corrPairing_le_count_smul IDENTICAL after d-replacement
```

### Target statements (extracted from the file by script)
```lean
theorem gueP_prod_map_ouMat (d L W : ℕ) [NeZero L] [NeZero W] (t : ℝ) (ht : 0 ≤ t) :
    ((gueP d L W).prod (gueP d L W)).map
        (fun ω : Ω d L W × Ω d L W =>
          Real.exp (-t / 2) • Xmat d L W ω.1 +
            Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω.2) =
      (gueP d L W).map (Xmat d L W)

theorem integral_kPoint_ouMat_cond {d : ℕ} {sz : Sizes d} (M : UNModel sz) (n : ℕ) (t : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (hO : Continuous O) (hOc : HasCompactSupport O) (E : ℝ) :
    ∫ ω, kPoint k O E (ouMat_isHermitian M n t ω).eigenvalues ∂(ouP M n) =
      ∫ ω₁, (∫ ω₂, kPoint k O E
          (dbmMat_isHermitian d (sz.L n) (sz.W n)
            (fun i => Real.exp (-t / 2) * (M.herm n ω₁).eigenvalues i)
            (1 - Real.exp (-t)) ω₂).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) ∂M.μ

theorem Step1Cond_gueMatPairing_eq_integral (d L W : ℕ) [NeZero L] [NeZero W] {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O) (E : ℝ) :
    ∫ ω, kPoint k O E (Xmat_isHermitian d L W ω).eigenvalues ∂(gueP d L W) =
      ∫ ω₁, (∫ ω₂, kPoint k O E
          (dbmMat_isHermitian d L W
            (fun i => Real.exp (-t / 2) * (Xmat_isHermitian d L W ω₁).eigenvalues i)
            (1 - Real.exp (-t)) ω₂).eigenvalues ∂(gueP d L W)) ∂(gueP d L W)

theorem Step1Cond_scaledPairing_lipschitz {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O)
    {ρmin ρmax : ℝ} (h0 : 0 < ρmin) (h1 : ρmin ≤ ρmax) :
    ∃ Q : (Fin k → ℝ) → ℝ, (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q) ∧
      0 ≤ Q ∧ ∃ C : ℝ, ∀ {Ω' : Type}
      [MeasurableSpace Ω'] (Pm : Measure Ω') [IsProbabilityMeasure Pm] {n : Type} [Fintype n]
      [DecidableEq n] (Hm : Ω' → Matrix n n ℂ), Measurable Hm → ∀ (hH : ∀ ω, (Hm ω).IsHermitian)
      (E ρ ρ' : ℝ), ρ ∈ Set.Icc ρmin ρmax → ρ' ∈ Set.Icc ρmin ρmax →
        |ρ ^ k * (∫ ω, kPoint k (fun β => O (fun j => ρ * β j)) E (hH ω).eigenvalues ∂Pm) -
            ρ' ^ k * (∫ ω, kPoint k (fun β => O (fun j => ρ' * β j)) E (hH ω).eigenvalues ∂Pm)| ≤
          C * |ρ - ρ'| * ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm

theorem Step1Cond_exists_dominating_testFun {k : ℕ} {Q : (Fin k → ℝ) → ℝ}
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q)
    (ρmin ρmax : ℝ) :
    ∃ Q' : (Fin k → ℝ) → ℝ, (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q' ∧ HasCompactSupport Q') ∧
      0 ≤ Q' ∧
      ∀ ρ ∈ Set.Icc ρmin ρmax, ∀ β : Fin k → ℝ, Q β ≤ Q' (fun j => ρ * β j)

theorem Step1Cond_corrPairing_le_count {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω')
    [IsProbabilityMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n] (Hm : Ω' → Matrix n n ℂ)
    (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) (hk : k < Fintype.card n)
    {Q : (Fin k → ℝ) → ℝ} (hQ0 : 0 ≤ Q) {R : ℝ}
    (hQR : ∀ β, Q β ≤ Set.indicator (Set.univ.pi fun _ : Fin k => Set.Icc (-R) R)
      (fun _ => (1 : ℝ)) β)
    (E : ℝ) :
    ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm ≤
      ((Fintype.card n : ℝ) / ((Fintype.card n : ℝ) - k)) ^ k *
        ∫ ω, (((Finset.univ : Finset n).filter
          (fun i => |(hH ω).eigenvalues i - E| ≤ R / (Fintype.card n : ℝ))).card : ℝ) ^ k
          ∂Pm

theorem Step1Cond_exists_le_indicator {k : ℕ} {Q : (Fin k → ℝ) → ℝ}
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧ HasCompactSupport Q) :
    ∃ B R : ℝ, 0 < B ∧ 0 ≤ R ∧ ∀ β, Q β ≤ B * Set.indicator
      (Set.univ.pi fun _ : Fin k => Set.Icc (-R) R) (fun _ => (1 : ℝ)) β

theorem Step1Cond_corrPairing_le_count_smul {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsProbabilityMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    (Hm : Ω' → Matrix n n ℂ) (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    (hk : k < Fintype.card n) {Q : (Fin k → ℝ) → ℝ} (hQ0 : 0 ≤ Q) {B R : ℝ} (hB : 0 < B)
    (hQR : ∀ β, Q β ≤ B * Set.indicator (Set.univ.pi fun _ : Fin k => Set.Icc (-R) R)
      (fun _ => (1 : ℝ)) β)
    (E : ℝ) :
    ∫ ω, kPoint k Q E (hH ω).eigenvalues ∂Pm ≤
      B * ((Fintype.card n : ℝ) / ((Fintype.card n : ℝ) - k)) ^ k *
        ∫ ω, (((Finset.univ : Finset n).filter
          (fun i => |(hH ω).eigenvalues i - E| ≤ R / (Fintype.card n : ℝ))).card : ℝ) ^ k
          ∂Pm

```

### #print axioms (from the build of the worktree)
```
1002:0: 'RBM.Univ.integral_kPoint_ouMat_cond' depends on axioms: [propext, Classical.choice, Quot.sound]
1003:0: 'RBM.Univ.gueP_prod_map_ouMat' depends on axioms: [propext, Classical.choice, Quot.sound]
1004:0: 'RBM.Univ.Step1Cond_gueMatPairing_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
1005:0: 'RBM.Univ.Step1Cond_scaledPairing_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
1006:0: 'RBM.Univ.Step1Cond_exists_dominating_testFun' depends on axioms: [propext, Classical.choice, Quot.sound]
1007:0: 'RBM.Univ.Step1Cond_corrPairing_le_count' depends on axioms: [propext, Classical.choice, Quot.sound]
1008:0: 'RBM.Univ.Step1Cond_exists_le_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
1009:0: 'RBM.Univ.Step1Cond_corrPairing_le_count_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Compiled nonempty instances (`examples` in the file, namespace `RBM.Univ.Step1CondCheck`, `d = 3`, `L = 3`, `W = 1`, `N = 27`, `k = 1`)
The constant sequence `step1Cond_szC : Sizes 3` (`L = 3`, `W = 1`) is the carrier of the model instance; the other seven endpoints are applied at `gueP 3 3 1`/`Xmat 3 3 1`. Lines of the `example`s and of their proof terms (script):
```
$ grep -n "^example\|^  Step1Cond_\|^  integral_kPoint\|^  gueP_prod\|^  exact ⟨Q, C\|^def step1Cond_szC" RBM3D/Universality/Step1Cond.lean
916:example :
924:  integral_kPoint_ouMat_cond (UNModel.band step1Cond_szC) 0 1 1 step1Cond_hat step1Cond_hat_cont
928:example :
933:  gueP_prod_map_ouMat 3 3 1 1 zero_le_one
936:example :
943:  Step1Cond_gueMatPairing_eq_integral 3 3 1 zero_le_one 1 step1Cond_bump_testFun 0
947:example : ∃ (Q : (Fin 1 → ℝ) → ℝ) (C : ℝ),
960:  exact ⟨Q, C, hQ, hQ0, hC (gueP 3 3 1) (Xmat 3 3 1) step1Cond_measurable_Xmat_331
964:example : ∃ Q' : (Fin 1 → ℝ) → ℝ,
968:  Step1Cond_exists_dominating_testFun step1Cond_bump_testFun (1 / 2) 2
971:example :
977:  Step1Cond_corrPairing_le_count (gueP 3 3 1) (Xmat 3 3 1) step1Cond_measurable_Xmat_331
982:example : ∃ B R : ℝ, 0 < B ∧ 0 ≤ R ∧ ∀ β, (step1Cond_bump : (Fin 1 → ℝ) → ℝ) β ≤ B *
984:  Step1Cond_exists_le_indicator step1Cond_bump_testFun
987:example :
995:  Step1Cond_corrPairing_le_count_smul (gueP 3 3 1) (Xmat 3 3 1) step1Cond_measurable_Xmat_331
```

### Name-clash grep (new public names on `main`) and port citation
```
git grep -w integral_kPoint_ouMat_cond main -- RBM3D:        0 matches
git grep -w gueP_prod_map_ouMat main -- RBM3D:        0 matches
git grep -w Step1Cond_gueMatPairing_eq_integral main -- RBM3D:        0 matches
git grep -w Step1Cond_scaledPairing_lipschitz main -- RBM3D:        0 matches
git grep -w Step1Cond_exists_dominating_testFun main -- RBM3D:        0 matches
git grep -w Step1Cond_corrPairing_le_count main -- RBM3D:        0 matches
git grep -w Step1Cond_exists_le_indicator main -- RBM3D:        0 matches
git grep -w Step1Cond_corrPairing_le_count_smul main -- RBM3D:        0 matches
git grep -w step1Cond_szC main -- RBM3D:        0 matches
git grep -w step1Cond_hat main -- RBM3D:        0 matches
git grep -w step1Cond_bump main -- RBM3D:        0 matches
git grep -w Step1CondCheck main -- RBM3D:        0 matches
$ git diff --name-only main...t/T2183
RBM3D/Universality/Step1Cond.lean
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h  -> 9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/Step1Cond.lean
 RBM2D/Universality/Step1Cond.lean | 263 ++++++--------------------------------
 1 file changed, 38 insertions(+), 225 deletions(-)
$ git -C ../RBM2D show c9a24cf:RBM2D/Universality/Step1Cond.lean | wc -l  -> 947
```

### Narrative
* Source: RBM2D `Universality/Step1Cond.lean` at `c9a24cf` (947 lines), copied to the scratchpad and ported to `RBM3D/Universality/Step1Cond.lean` (1011 lines with instances). `L W` became `d L W`; `Ω`, `Idx`, `gueP`, `Xmat`, `gueVar`, `dbmMat` are the merged RBM3D ones; the `Rescale` section (the five rescaling/counting targets) is dimension-free and copied verbatim.
* Shape change forced by the merged vocabulary (stage 1a finding, paper-delta candidate T2183a): `ouMat` is model-indexed on `main` (`Pins.lean:150`). `integral_kPoint_ouMat_cond` is therefore stated for `M : UNModel sz`, `ouP M n`, with RHS over `M.μ` and `(M.herm n ω₁).eigenvalues`; `gueP_prod_map_ouMat` is stated for the explicit matrix `e^{-t/2} • Xmat ω.1 + √(1-e^{-t}) • Xmat ω.2` on `gueP.prod gueP`, which is RBM2D `ouMat` by definition. No hypothesis was added or removed; `hOc` is kept.
* Both are proved from one private lemma `Step1Cond_cond_general` (any probability space and measurable Hermitian family `H₀`); `Step1Cond_inner_eq` is the RBM2D proof with `Xmat x` replaced by a fixed Hermitian `H₀` (the proof only used that). `ouMat M n t ω` unfolds to `Step1Cond_mixMat (M.H n ω.1) t ω.2` by `rfl`.
* `Step1Cond_gue_interp_law` is a copy of the RBM2D proof with a private `Step1Cond_pairSample` in place of `ouSample L W` (on `main`, `ouSample` reads the first block through `slice sz n`, and the OU pair-law helper is private).
* The six remaining targets compare identical to the source after the `d`-replacement (script above).
* RBM2D `T1Stmt`/`T2Stmt` and their `_holds` theorems are not ported: `T1Stmt` is not statable verbatim for the model-indexed `ouMat`; the endpoint examples replace them. The RBM2D instances `Idx 3 3` (`N = 81`) became `Idx 3 3 1` (`N = 27`), `hat`/`bump` were renamed `step1Cond_hat`/`step1Cond_bump`.
* No new `Prop` definition is a premise of a theorem, so `RBM3D/Test/Axioms.lean` is untouched; the registry pre-check above exits 0.
* The hub adds `import RBM3D.Universality.Step1Cond` to `RBM3D.lean` at merge; the full `lake build` above is the worktree build before that import.

## (c) Verified Mathlib names (all compile in this file; taken from the RBM2D source, re-elaborated)
`gaussianReal_map_const_mul`, `gaussianReal_conv_gaussianReal`, `Measure.infinitePi_map_restrict`, `Measure.isProjectiveLimit_infinitePi`, `measurePreserving_arrowProdEquivProdArrow`, `Measure.pi_map_pi`, `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff`, `Matrix.charpoly_mul_comm`, `Matrix.isHermitian_conjTranspose_mul_mul`, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, `ContDiffBump`, `HasCompactSupport.exists_bound_of_continuous`, `Continuous.bounded_above_of_compact_support`, `Integrable.of_bound`, `integral_prod`, `measurable_pi_apply`. Absent as instance: `OpensMeasurableSpace (Matrix _ _ ℂ × Matrix _ _ ℂ)` (build error on the first attempt), hence the entrywise measurability proof of `Step1Cond_measurable_mixMat`.

## (d) Open issues and paper-delta candidates
* `T2183a` (shape of `ouMat`, not a mathematical difference): `integral_kPoint_ouMat_cond` is model-indexed (`ouP M n`, `M.μ`, `M.herm n`) instead of RBM2D `μ.prod (gueP L W)` with `Xmat_isHermitian ω₁`; `gueP_prod_map_ouMat` is stated for the explicit matrix instead of `ouMat L W t`. A consumer with a first block `gueP` uses `Step1Cond_gueMatPairing_eq_integral` (unchanged statement, with `d`).
* `Step1Cond_cond_general` is private; a downstream ticket that needs conditioning for a measurable Hermitian family that is not a `UNModel` needs it promoted (a new ticket, not done here).
* Ticket text says the source has 947 lines and 798 kept; RBM2D `HEAD` (`9e0f275`) differs from `c9a24cf` (diff stat above), the port is from `c9a24cf`.
