Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 03:25:27 UTC 2026

### (i) Exponent table

No exponent, threshold or probability constant enters T2247 (deterministic identities on finite matrices; no `3 ≤ d`, `3 ≤ L`, no `∀ᶠ n`). The constants are the numeric ones below; each was re-derived by hand (coordinate calculus on `G = (H - z)⁻¹`) and the Wirtinger/kernel rows checked numerically in (ii).

| quantity | value | constraint it must satisfy | slack |
|---|---|---|---|
| `d, L, W` | 3, 3, 2 | any `d`; `NeZero L`, `NeZero W` only (Fintype/`Idx`); no `3 ≤ d`, `3 ≤ L` hypothesis in targets 1-5 | `NeZero`: `L = 3 ≥ 1`, `W = 2 ≥ 1` |
| `N = Fintype.card (Idx d L W) = (W L)^d` | 216 | `card_Idx`; `N ≠ 0` (else `N⁻¹ = 0` both sides, still true) | `N = 216 > 0` |
| `lam` (variance parameter, `svarF d L W lam`) | 1/2 | any real (`svarF ≥ 0` for all `lam`; band `sz.lam n`, model-generic `K.lamV sz n`, BA `0`) | none needed; at `lam = 1/2`: `a = (1+2d lam²)⁻¹ = 0.4`, `b = lam² a = 0.1`, `a + 2d b = 1` |
| `S_{x0 x1}`, `x0 = 0`, `x1 = Pi.single 0 1` | `a/W^d = 0.05` (same block: `val//W = 0`) | `x0 ≠ x1` in `Z_6^3` (`1 ≠ 0` in `ZMod 6`) | `S° = 0.05 - 1/216 = 0.0453704 > 0` |
| `Im z` (targets 2b-2e, 3a-3d) | `z = I`: 1; `2I`: 2 (random run: 0.5) | `z.im ≠ 0` (makes `H - z` invertible for Hermitian `H`: `isUnit_sub_smul_one_of_im_ne_zero`, and along `H + tA`) | `|Im z| ≥ 1` at the instance |
| Hermitian hypotheses | `H = 1`, `A = Bmat` (Hermitian iff `i ≠ j ∨ b = true`) | `H.IsHermitian`, `A.IsHermitian`; `H + (t:ℂ)•A` Hermitian for real `t` | `Bmat x0 x1 false`, `Bmat x0 x0 true` Hermitian; `Bmat x0 x0 false` is not (excluded by target 1c, never used) |
| first line derivative of `m = N⁻¹ tr G` | `-N⁻¹ tr(GAG)` | `d/dt G(H+tA) = -GAG` (target 2b), trace linear | exact (hand check) |
| second line derivative | `+2 N⁻¹ tr(GAGAG)` | `d/dt (GAG) = -(GAG)AG - GA(GAG)`, so `d/dt(-N⁻¹ tr GAG) = +2N⁻¹ tr(GAGAG)` (2d) | exact |
| product second derivative | `Σ_i [ (∏_{j≠i} f_j) f_i'' + (Σ_{j≠i} (∏_{k≠i,j} f_k) f_j') f_i' ]` | `f_i` differentiable everywhere, `f_i'` differentiable at `0` (2a) | exact (Leibniz; `s = ∅` gives `0 = 0`) |
| Wirtinger weights | off-diagonal `1/4 (∂_a² + ∂_b²)`, diagonal `∂_a²`; first derivative `1/2 (D_true - i D_false)` | `B_true = E_ij+E_ji`, `B_false = iE_ij - iE_ji` | exact (hand check below) |
| 3d entry formula | `N⁻¹ Im((G²)_ii G_jj + (G²)_jj G_ii)` | diag: `tr(G E_ii G E_ii G) = G_ii (G²)_ii`, times `2N⁻¹`; off-diag: `B_t G B_t`, `B_f G B_f` cross terms `G_ij (G²)_ij`, `G_ji (G²)_ji` cancel, remaining `2(G_jj (G²)_ii + G_ii (G²)_jj)`, times `2N⁻¹ · 1/4` | exact |
| 3b formula `(i N⁻¹/2)((G²)_ji - conj (G²)_ij)` | with `P = (G²)_ij`, `Q = (G²)_ji`: `D_t = -N⁻¹ Im(P+Q)`, `D_f = -N⁻¹ Re(Q-P)`, `1/2(D_t - i D_f) = (iN⁻¹/2)(Q - conj P)`; diag: `-N⁻¹ Im P_ii = (iN⁻¹/2)(P_ii - conj P_ii)` | `Bmat` tags as in target 1 | exact |
| 3c `conj (G²)_ij = (G(z̄)²)_ji` | `G(z)^H = G(z̄)` for Hermitian `H` | `H.IsHermitian` (hypothesis present in 3c) | exact |
| 4 bridge `signedGreen = Gres` | `(H - z•1)⁻¹ = Ring.inverse (H - z•1)` (`Matrix.nonsing_inv_eq_ringInverse`) | no Hermitian hypothesis needed (both are the nonsingular inverse; `σ = false` uses `z̄` on both sides) | holds for every `H`, `z` |
| 4 casts | `(N:ℂ)⁻¹ = (((W*L)^d : ℕ):ℂ)⁻¹`; `↑(svarF - (N:ℝ)⁻¹) = ↑svarF - (N:ℂ)⁻¹ = scirc`; `N⁻¹*N⁻¹ = (N⁻¹)^2` | `card_Idx`, `push_cast`, `sq`; sums `Σ_σ Σ_τ` = `Σ b₁ Σ b₂`; matrix entries `(G z σ * G z σ) a a`, `(G z τ) b b` and `(G z₁ σ²) a b · (G z₂ τ²) b a` agree term by term with `Pins.lean:617-629` | token-identical (checked below) |
| consumer shape `UNEMCTE2` (`Pins.lean:675, 680`) | `L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat …) (z u)`, `L2t … (z u) (z v)` | the bridges at `lam := sz.lam n`, `H := ouMat …` are exactly these arguments; model-generic `PinsK.lean:351, 356` with `lam := K.lamV sz n` | token-identical |
| `Gres` bridge (RBM2D `rfl` sites, c9a24cf text, `grep -n rfl`) | `stieltjesN K z = N⁻¹ * (Gres K z true).trace`, `Gres K z true = Ring.inverse (K - z•1) = (K - z•1)⁻¹ = green K z` | propositional (`Matrix.nonsing_inv_eq_ringInverse`), not `rfl`; the `stieltjesN`-unfolding `rfl` sites are c9a24cf `:480`, `:494`, `:640` (as the ticket says); `:508` is a `fderiv ∘ imCLM` composition and `:755` a function-composition `rfl`, neither unfolds `stieltjesN` | one bridge lemma `Gres H z true = green H z` (template `InjSum.lean:76-78`), no mathematical change |

Quantifier note: nothing here is stated with `∀ᶠ N`; all targets are `∀ d L W` (or generic finite `n`), as in RBM2D.

### (ii) One concrete nondegenerate instance

Data: `d = 3, L = 3, W = 2, N = 216, lam = 1/2`; `H = 1` (Hermitian), `z = I` and `2I` (`Im ≠ 0`), `x0 = 0 ≠ x1 = Pi.single 0 1`, `A = Bmat x0 x1 b` (Hermitian); line instances at `n = Fin 2`, `H = A = 1`, `t = 0`. No external hypothesis (no pin); every hypothesis of targets 1-5 is a Mathlib predicate (`IsHermitian`, `im ≠ 0`, `i ≠ j`) and holds at this data. A second, generic Hermitian data point (random `H`, `N = 216`, `z = 0.3+0.5i`, `z₂ = -0.2+0.9i`) tests the nonzero values: finite differences (step `3e-4`) of `Im m` against the formulas of 3a, 3b, 3d, 2e, and `paperL1Kernel`/`paperL2Kernel` (built from `signedGreen`, `S - N⁻¹`, `card`) against `L1t`/`L2t` (built from `Gres`, `scirc`, `(W L)^d`). External-hypothesis limit computation: not applicable (no external hypothesis).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2247/inst.py` (numpy; `svarF` rebuilt from `sbKernelR`, `zdist`, `blk`, `Defs/Block.lean:74`, `Defs/Lattice.lean:25,71`, `Defs/Sizes.lean:50`)

```
N = 216  a = 0.4  b = 0.1  a+2d*b = 1.0
S symmetric: True  row sums = 1.0 1.0  S>=0: True
x0 != x1: True  S[x0,x1] = 0.05  Scirc[x0,x1] = 0.04537037037037037
Bmat hermitian: (x0,x1,false) True  (x0,x0,true) True  (x0,x0,false) False
swap true: True  swap false: True
-- random Hermitian H, N=216, z=0.3+0.5i  Hermitian: True  Im z = 0.5
3d wirtSecond FD = -0.005123863062234731  formula = -0.005123862594285742  relerr = 9.132738826915879e-08
3b wirtFirst  FD = (-8.474141962218815e-05-7.072252487342705e-05j)  formula = (-8.474147690780599e-05-7.072256464229785e-05j)  relerr = 6.318118283792705e-07  3c adjoint form relerr = 7.380414041319058e-15
3a product wirtSecond FD = -0.007320863359971954  expansion = -0.007320862554648733  relerr = 1.100038710499631e-07
2e line second (diag A=B(x0,x0,true)): FD = -0.008503268459728968  expansion = -0.008503266996425677
paperL1Kernel = 0.0008142113765796982  L1t = 0.0008142113765796982  diff = 0.0
paperL2Kernel = 0.0002620840980995531  L2t = 0.0002620840980995531  diff = 0.0  L1t>0: True  L2t>0: True
conj bridge: ||G(conj z) - G(z)^H|| = 2.7822109252321576e-15
-- instance H=1, z=I: inst_entry wirtSecond FD = 0.002314815006343452  formula = 0.0023148148148148147  exact 1/(2N) = 0.0023148148148148147
   Im z = 1.0  Im(2I) = 2.0   G=(1+i)/2: True
   inst_wirtFirst FD = 0j  formula = 0j
   L1t at H=1, z=I = 1.7009334969074227e-16  (row sums of S - 1/N vanish, so both sides are 0 here; random-H run above has L1t > 0)
```

Reading: `S` has row sums 1, symmetric, nonnegative; `Bmat` swap rules and Hermitian cases hold as in target 1; relative errors of the Hessian formulas are ≤ 1e-6 (finite-difference noise); `3c` form equals `3b` to 1e-14; the bridge kernels agree (`diff = 0`; they are the same arithmetic after `signedGreen = Gres`, `card = (W L)^d`; the content of the Lean bridge is that identification). At `H = 1`: `inst_wirtFirst` is `0 = 0` (off-diagonal of `G²` vanishes) and `L1t` is `0` (printed `1.7e-16`; row sums of `S°` vanish), so those instance equalities are true but carry numerically trivial values; the hypotheses are nondegenerate, and the random-`H` run shows the same identities at nonzero values. `inst_entry` (`wirtSecond` at `H = 1`) has the exact nonzero value `1/(2N) = 1/432`.

### Verdicts

- Target 1 (`Bmat_swap_true`, `Bmat_swap_false`, `Bmat_isHermitian_of_ne_or`): PASS (entrywise check: `i = j` and `i ≠ j`; `Bmat i i false = iE_ii` is non-Hermitian, correctly excluded).
- Target 2 (`hasDerivAt_deriv_finset_product_expansion`, `…_green_hermitianLine`, `…_stieltjesN_hermitianLine`, `…_stieltjesFirstVariation`, `fderiv_fderiv_stieltjesImProduct_hermitianLine`): PASS (formulas `-GAG`, `-N⁻¹tr GAG`, `2N⁻¹ tr GAGAG`, Leibniz expansion; `K ↦ Im m(K,z)` analytic near Hermitian `H` since `H - z` is invertible, so `fderiv ∘ fderiv` along `A, A` is the line second derivative).
- Target 3 (`wirtSecond_stieltjesImProduct_expansion`, `stieltjesImWirtingerFirst_entry_formula`, `…_adjoint_formula`, `wirtSecond_stieltjesIm_entry_formula`): PASS (hand derivation in table rows 3b-3d; numerics above).
- Target 4 (`centeredVarianceEntry_symm`, `…_cast`, `signedGreen_eq_Gres`, `paperL1Kernel_eq_L1t`, `paperL2Kernel_eq_L2t`): PASS (true for every `H`; the RBM2D `IsHermitian` hypothesis is not needed).
- Target 5 (instances at `d = 3, L = 3, W = 2`): PASS (all hypotheses hold at the data above).
- Observation for stage 1b: RBM2D working tree HEAD `9e0f275` has a trimmed `Universality/OUHessian.lean` (1084 lines); the ticket's source is the `c9a24cf` version (1242 lines), obtained with `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Universality/OUHessian.lean`.

Overall verdict: PASS.

## (b) Script output — Tue Oct  6 03:33:41 UTC 2026

### Build (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2247, branch t/T2247, commit 6386334)
```
$ lake build RBM3D.Universality.OUHessian 2>&1 | grep -n "OUHessian\|^error"; tail -1
Build completed successfully (3350 jobs).
$ lake build   # whole library (root RBM3D.lean does not import the new module yet; the hub adds the import at merge)
Build completed successfully (4050 jobs).
exit 0
$ git diff --stat main...t/T2247
 RBM3D/Universality/OUHessian.lean | 1322 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1322 insertions(+)
$ git diff main -- RBM3D/Test/Axioms.lean | wc -l
       0
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/OUHessian.lean; echo $?
grep exit 1
```

### Axioms (scratch file: import RBM3D + RBM3D.Universality.OUHessian + `#print axioms`; all 24 outputs compared by script)
```
declarations printed: 24; distinct axiom sets: 1: {'propext, Classical.choice, Quot.sound'}
Bmat_swap_true, Bmat_swap_false, Bmat_isHermitian_of_ne_or, hasDerivAt_deriv_finset_product_expansion, hasDerivAt_green_hermitianLine, hasDerivAt_stieltjesN_hermitianLine, hasDerivAt_stieltjesFirstVariation, fderiv_fderiv_stieltjesImProduct_hermitianLine, wirtSecond_stieltjesImProduct_expansion, stieltjesImWirtingerFirst_entry_formula, stieltjesImWirtingerFirst_adjoint_formula, wirtSecond_stieltjesIm_entry_formula, centeredVarianceEntry_symm, centeredVarianceEntry_cast, signedGreen_eq_Gres, paperL1Kernel_eq_L1t, paperL2Kernel_eq_L2t, OUHessianInst.inst_directions, OUHessianInst.inst_entry, OUHessianInst.inst_product, OUHessianInst.inst_wirtFirst, OUHessianInst.inst_kernels, OUHessianInst.inst_green_line, OUHessianInst.inst_stieltjes_line
```

### Registry pre-check (CLAUDE.md §20 (2); scratch `import RBM3D` + `import RBM3D.Universality.OUHessian` + `#assert_rbm_axioms`)
```
$ lake env lean reg.lean; echo $?   -> exit 0 (no error, no unregistered premise)
$ diff <(output without OUHessian) <(output with OUHessian)
1c1
< axiom audit: 7283 theorems, 2459 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 7314 theorems, 2473 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```

### Target statements (extracted by script from RBM3D/Universality/OUHessian.lean; section variables: `(d L W : ℕ) [NeZero L] [NeZero W]` resp. `{n : Type*} [Fintype n] [DecidableEq n]`)
```
theorem Bmat_swap_true (i j : Idx d L W) :
    RBM.Green.Bmat d L W j i true = RBM.Green.Bmat d L W i j true

theorem Bmat_swap_false {i j : Idx d L W} (hij : i ≠ j) :
    RBM.Green.Bmat d L W j i false = -RBM.Green.Bmat d L W i j false

theorem Bmat_isHermitian_of_ne_or {i j : Idx d L W} {b : Bool} (h : i ≠ j ∨ b = true) :
    (RBM.Green.Bmat d L W i j b).IsHermitian

theorem hasDerivAt_deriv_finset_product_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f fp : ι → ℝ → ℝ) (fpp : ι → ℝ)
    (hf : ∀ i ∈ s, ∀ t, HasDerivAt (f i) (fp i t) t)
    (hfp : ∀ i ∈ s, HasDerivAt (fp i) (fpp i) 0) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ => ∏ i ∈ s, f i u) t)
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, f j 0) * fpp i +
          (∑ j ∈ s.erase i,
            (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0) * fp i 0)) 0

theorem hasDerivAt_green_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z)
      (-(RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z)) t

theorem hasDerivAt_stieltjesN_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => stieltjesN (H + (s : ℂ) • A) z)
      (-((Fintype.card n : ℂ)⁻¹) *
        (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z).trace) t

theorem hasDerivAt_stieltjesFirstVariation {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => -((Fintype.card n : ℂ)⁻¹) *
        (RBM.green (H + (s : ℂ) • A) z * A * RBM.green (H + (s : ℂ) • A) z).trace)
      (2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z * A *
          RBM.green (H + (t : ℂ) • A) z).trace) t

theorem fderiv_fderiv_stieltjesImProduct_hermitianLine {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ) (hH : H.IsHermitian) (hA : A.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ =>
      ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ))) H A A =
      ((stieltjesImProductLineSecond s H A z : ℝ) : ℂ)

theorem wirtSecond_stieltjesImProduct_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (hH : H.IsHermitian) (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0)
    (a b : Idx d L W) :
    wirtSecond d L W
        (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b =
      if a = b then
        (stieltjesImProductLineSecond s H (RBM.Green.Bmat d L W a a true) z : ℂ)
      else
        (1 / 4 : ℝ) •
          ((stieltjesImProductLineSecond s H (RBM.Green.Bmat d L W a b true) z : ℂ) +
            (stieltjesImProductLineSecond s H (RBM.Green.Bmat d L W a b false) z : ℂ))

theorem stieltjesImWirtingerFirst_entry_formula
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Idx d L W) :
    stieltjesImWirtingerFirst d L W H z i j =
      (Complex.I * (Fintype.card (Idx d L W) : ℂ)⁻¹ / 2) *
        ((RBM.green H z * RBM.green H z) j i -
          (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j))

theorem stieltjesImWirtingerFirst_adjoint_formula
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Idx d L W) :
    stieltjesImWirtingerFirst d L W H z i j =
      (Complex.I * (Fintype.card (Idx d L W) : ℂ)⁻¹ / 2) *
        ((RBM.green H z * RBM.green H z) j i -
          (RBM.green H ((starRingEnd ℂ) z) * RBM.green H ((starRingEnd ℂ) z)) j i)

theorem wirtSecond_stieltjesIm_entry_formula
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Idx d L W) :
    wirtSecond d L W (fun K => ((stieltjesN K z).im : ℂ)) H i j =
      ((((Fintype.card (Idx d L W) : ℂ)⁻¹) *
        ((RBM.green H z * RBM.green H z) i i * (RBM.green H z) j j +
          (RBM.green H z * RBM.green H z) j j * (RBM.green H z) i i)).im : ℂ)

theorem centeredVarianceEntry_symm (lam : ℝ) (a b : Idx d L W) :
    centeredVarianceEntry d L W lam a b = centeredVarianceEntry d L W lam b a

theorem centeredVarianceEntry_cast (lam : ℝ) (a b : Idx d L W) :
    ((centeredVarianceEntry d L W lam a b : ℝ) : ℂ) = scirc d L W lam a b

theorem signedGreen_eq_Gres (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) :
    signedGreen H z σ = RBM.Gauss.Gres H z σ

theorem paperL1Kernel_eq_L1t (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) :
    paperL1Kernel d L W lam H z = L1t d L W lam H z

theorem paperL2Kernel_eq_L2t (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ) :
    paperL2Kernel d L W lam H z₁ z₂ = L2t d L W lam H z₁ z₂

```

### Statement check against the release check (scratch cmp.lean = docs/tickets/checks/T2247-check.lean sections 1-2 with `import RBM3D.Universality.OUHessian`, sections 3 replaced by the examples below)
```
$ lake env lean cmp.lean; echo $?        -> 0, no error
26 examples `example : T2247Check.T2247_<name> := @RBM.Univ.<name>` (or `RBM.Univ.OUHessianInst.<name>`): Bmat_swap_true, Bmat_swap_false, Bmat_isHermitian_of_ne_or, hasDerivAt_deriv_finset_product_expansion, hasDerivAt_green_hermitianLine, hasDerivAt_stieltjesN_hermitianLine, hasDerivAt_stieltjesFirstVariation, fderiv_fderiv_stieltjesImProduct_hermitianLine, wirtSecond_stieltjesImProduct_expansion, stieltjesImWirtingerFirst_entry_formula, stieltjesImWirtingerFirst_adjoint_formula, wirtSecond_stieltjesIm_entry_formula, centeredVarianceEntry_symm, centeredVarianceEntry_cast, signedGreen_eq_Gres, paperL1Kernel_eq_L1t, paperL2Kernel_eq_L2t, inst_directions, inst_entry, inst_product, inst_wirtFirst, inst_kernels, inst_green_line, inst_stieltjes_line, RBM.Univ.OUHessianInst.x0, RBM.Univ.OUHessianInst.x1
12 examples `@RBM.Univ.<vocab> = @T2247Check.<vocab> := rfl` for coordD1, coordD2, wirtSecond, centeredVarianceEntry, paperL1Kernel, paperL2Kernel, signedGreen, stieltjesImWirtingerFirst, stieltjesImAlong, stieltjesImLineFirst, stieltjesImLineSecond, stieltjesImProductLineSecond
consumer shape at the band data (check section 3): paperL1Kernel d (sz.L n) (sz.W n) (sz.lam n) H z = L1t d (sz.L n) (sz.W n) (sz.lam n) H z := paperL1Kernel_eq_L1t ...  (compiles; Pins.lean:675 shape)
```

### Compiled nonempty instances (target 5; namespace RBM.Univ.OUHessianInst; d=3, L=3, W=2, lam=1/2, H=1, z=I, 2I; every hypothesis discharged, no premise)
```
theorem x0_ne_x1 := (statement = check 2.6 `T2247_x0_ne_x1`)
  intro h
  have h0 := congrFun h 0
  have h1 : (0 : ZMod 6) = 1 := by simpa [x0, x1] using h0
  exact absurd h1 (by decide)
theorem inst_directions := (statement = check 2.6 `T2247_inst_directions`)
  ⟨x0_ne_x1, Bmat_swap_true 3 3 2 x0 x1, Bmat_swap_false 3 3 2 x0_ne_x1,
    Bmat_isHermitian_of_ne_or 3 3 2 (Or.inl x0_ne_x1),
    Bmat_isHermitian_of_ne_or 3 3 2 (Or.inr rfl)⟩
theorem inst_entry := (statement = check 2.6 `T2247_inst_entry`)
  ⟨paperL1Kernel_eq_L1t 3 3 2 (1 / 2) 1 Complex.I,
    wirtSecond_stieltjesIm_entry_formula 3 3 2 1 Matrix.isHermitian_one Complex.I (by simp) x0 x1⟩
theorem inst_product := (statement = check 2.6 `T2247_inst_product`)
  wirtSecond_stieltjesImProduct_expansion 3 3 2 Finset.univ 1 Matrix.isHermitian_one
    ![Complex.I, 2 * Complex.I]
    (by
      intro i _
      fin_cases i <;> simp)
    x0 x1 |>.trans (ite_eq_right x0_ne_x1)
theorem inst_wirtFirst := (statement = check 2.6 `T2247_inst_wirtFirst`)
  stieltjesImWirtingerFirst_adjoint_formula 3 3 2 1 Matrix.isHermitian_one Complex.I (by simp) x0 x1
theorem inst_kernels := (statement = check 2.6 `T2247_inst_kernels`)
  ⟨RBM.Gauss.card_Idx 3 3 2 ▸ by norm_num,
    centeredVarianceEntry_symm 3 3 2 (1 / 2) x0 x1,
    centeredVarianceEntry_cast 3 3 2 (1 / 2) x0 x1,
    signedGreen_eq_Gres _ _ _,
    paperL2Kernel_eq_L2t 3 3 2 (1 / 2) 1 Complex.I (2 * Complex.I)⟩
theorem inst_green_line := (statement = check 2.6 `T2247_inst_green_line`)
  hasDerivAt_green_hermitianLine (H := (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (A := (1 : Matrix (Fin 2) (Fin 2) ℂ)) Matrix.isHermitian_one Matrix.isHermitian_one
    Complex.I (by simp) 0
theorem inst_stieltjes_line := (statement = check 2.6 `T2247_inst_stieltjes_line`)
  hasDerivAt_stieltjesN_hermitianLine (H := (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (A := (1 : Matrix (Fin 2) (Fin 2) ℂ)) Matrix.isHermitian_one Matrix.isHermitian_one
    Complex.I (by simp) 0
-- plus four unnamed `example`s: target 2a (ι = Fin 2), 2d, 2e (n = Fin 2, H = A = 1, z = ![I, 2I]), 3b (d=3,L=3,W=2)
```

### Name-clash grep (new public names incl. the instance namespace; `git grep -nw <name> main -- RBM3D RBM3D.lean`, Probe excluded)
```
  main:RBM3D/Green/IBP.lean:406:`Bmat_swap_true`, `Generator:916`). -/
  main:RBM3D/Green/IBP.lean:421:`Bmat j i false = -Bmat i j false` (RBM1D `Bmat_swap_false`, `Generator:930`). -
(all other names: 0 hits; total names checked:       38)
$ grep -rn "theorem hasDerivAt_line\|theorem isHermitian_add_realSmul\|theorem hasDerivAt_lineInverse\|def gSel\|def Scirc" RBM3D  -> no output (no public twin; none added)
```

### Port (RBM2D, read-only)
```
source: RBM2D/Universality/OUHessian.lean at c9a24cf (git show; 1242 lines), RBM2D/Gauss/Envelope.lean:144-166, 266-273 at c9a24cf; c9a24cf = c9a24cf
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/OUHessian.lean RBM2D/Gauss/Envelope.lean   (HEAD = 9e0f275, trimmed versions)
 RBM2D/Gauss/Envelope.lean         | 175 +++-----------------------
 RBM2D/Universality/OUHessian.lean | 250 +++++++-------------------------------
 2 files changed, 63 insertions(+), 362 deletions(-)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Universality/OUGenerator.lean | grep -n "import.*OUHessian"
7:import RBM2D.Universality.OUHessian
```

Narrative (facts from the files above): the file is RBM2D `OUHessian.lean` (c9a24cf) with `Idx d L W`, `CoordF`, `usedCoords d L W`, `svarF d L W lam`; targets 1-5 compile with the check's statements (defeq examples above). New work: private bridges `OUHessian_Gres_true`, `OUHessian_stieltjesN_eq` (replaces the three RBM2D `rfl` unfoldings of `stieltjesN` at c9a24cf `:480, :494, :640` by a `rw`; the `:459` `fderiv ∘ imCLM` `rfl` is kept), `OUHessian_green_conj` (replaces `Gsig_conjTranspose`), private copies of the three line helpers, `signedGreen_eq_Gres` (all `H`; `IsHermitian` hypothesis of RBM2D bridges dropped), `hc : c.im = 0` reproved by `Complex.inv_im`, `Complex.natCast_im` (simp now unfolds `card (Idx d L W)`). Not targets: no pin proved or stated (`UNEMCTE2`, `UNEMCTE2Row`, `UNJakUywRow`, `UNUnivMainRow` stay owed); no `card_Idx_eq`, `gSel`, `Scirc` added; no merged file changed; `RBM3D/Test/Axioms.lean` untouched (diff 0 lines; owed count unchanged, registry output differs only in the theorem/definition count line). The instance equalities `inst_wirtFirst` and the `L1t` part of `inst_entry` hold with numerically trivial values at `H = 1` (preflight (ii): off-diagonal of `G^2` vanishes, row sums of `S°` vanish); `inst_entry` second conjunct (1/(2N)), `inst_product`, `inst_green_line`, `inst_stieltjes_line` and the Hermitian/non-equal-site hypotheses are nondegenerate, and no hypothesis is left open. Numerical sanity (vi) is preflight's script output in (a). Preflight section (a) is unchanged; no (a′) needed.

## (c) Verified Mathlib names (all compile in the file; `lake build RBM3D.Universality.OUHessian`)
HasDerivAt.fun_finsetProd, HasDerivAt.sum, hasFDerivAt_ringInverse, analyticAt_inverse, Finset.analyticAt_fun_prod, Complex.imCLM, Complex.ofRealCLM, ContinuousLinearMap.mulLeftRight, Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv, Matrix.isHermitian_one, Matrix.trace_single_mul, Matrix.traceLinearMap, Ring.inverse_unit, Complex.inv_im, Complex.natCast_im, ite_eq_right. Verified deprecated: `if_neg` (use `ite_eq_right`). Verified not `@[simp]`: `RBM.Gauss.card_Idx` (build warning when used as `-card_Idx`). Verified absent in RBM3D: public `hasDerivAt_line`, `hasDerivAt_lineInverse`, `isHermitian_add_realSmul`, `gSel`, `Scirc` (grep above).

## (d) Open issues and paper-delta candidates
- T2247a (design, no paper statement; as in the ticket, confirmed): UN-16 precedes UN-15 (`OUGenerator.lean:7` at c9a24cf imports `OUHessian`); RBM2D `Gauss.hasDerivAt_line`, `_lineInverse`, `isHermitian_add_realSmul` are private copies here; `paperL1Kernel_eq_L1t`, `paperL2Kernel_eq_L2t` have no `IsHermitian` hypothesis (`signedGreen_eq_Gres` holds for every `H`).
- Observation: RBM2D HEAD `9e0f275` has trimmed versions of both source files; this port follows c9a24cf as the ticket says.
- No T2247b: every statement elaborated as the check states it; no hypothesis was added or removed.
- Hub merge note: add `import RBM3D.Universality.OUHessian` after the last `import` line of `RBM3D.lean`; nothing to merge in `Test/Axioms.lean`.
