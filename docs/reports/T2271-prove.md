Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 08:16:05 UTC 2026

### (i) Exponent table

Notation: `N = (W L)^d`, `lam` free real, `𝔡 > 0`, `p` the per-block QUE bound, `θ` the window bound on `|M_{αβ}|`.
`M_{αβ}(a₀) = ∑_b SBR(b,a₀) ((N/W^d) ∑_{x∈[b]} conj ψ_β ψ_α − δ_{αβ})` (`blockM2`; `JakSpectral.lean:227`, `Pins.lean:392`).

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | weights `w_b = SBR(b,a₀)` | `≥ 0`, `∑_b w_b = 1` (`sum_SBR_row` + `SBR_comm`, `3 ≤ L`) | needed for `‖∑ w_b u_b‖ ≤ max_{w_b≠0} ‖u_b‖` | exact; `3 ≤ L` only |
| 2 | support of `w` | `≤ 2d+1` blocks (`unBadY_card_le`, `3 ≤ L`) | union bound constant | `= 7` at `d=3, L=3` (script: support 7 per row) |
| 3 | `blockM2_eq` | `M(siteBlock y,α,β) = N ∑_x ψ_α conj ψ_β S°_{xy}`; `svarF x y = W^{-d} SBR(blk x, blk y)`; `−N·N⁻¹∑_x ψ_α conj ψ_β = −δ_{αβ}` cancels the `−δ` of `blockM2` | `3 ≤ L`; orthonormality | exact identity (script: diff `5.6e-16`) |
| 4 | window of target 3 | `\|λ−E\| ≤ N⁻¹W^{𝔡/3}` must lie in `queWindow(ε₀=𝔡/3)`: `N⁻¹W^{𝔡/3} ≤ W^{-𝔡/3}(lam W^{d/2}/N)` | `W^{-d/2+𝔡} ≤ lam` (eq:WO), `1 ≤ W` | `W^{𝔡/3}` (needs only `W^{2𝔡/3−d/2} ≤ lam`); `un_window_sub` is exactly this |
| 5 | threshold of target 3 | `W^{-𝔡/6} ≤ ‖u_b‖` ⟺ `W^{d−𝔡/6}/N ≤ ‖S_b−(W^d/N)δ‖` (`W^{d−𝔡/6} = W^d W^{-𝔡/6}`, `u_b=(N/W^d)(S_b−(W^d/N)δ)`) | `queBadMat` at `(ε₀,c) = (𝔡/3, 𝔡/6)`; `0<c<ε₀`, `c<𝔡/5` (`un_que_params`) | `ε₀−c = 𝔡/6`, `𝔡/5−c = 𝔡/30` |
| 6 | pair index in `queBadMat` | `blockM2` has `star ψ_β · ψ_α`, `if α = β`; `queBadMat` has `star(ψ i)·ψ j`, `if i = j`: `i=β, j=α` | `α=β` vs `β=α` are the same proposition up to `eq_comm` | exact |
| 7 | union bound | `P(bad) ≤ ∑_{b∈supp} p = (2d+1) p` | `hp : ∀ b, P{queBadMat b} ≤ p` | `(2d+1)p`, same constant as merged `measure_bad_le_of_queBadMat` |
| 8 | `y`-term expansion (target 2) | `∑_x (G₁²)_{xy} S°_{xy} (G₂²)_{yx} = N⁻¹ ∑_{αβ} p_α²q_β² M_{αβ} conj ψ_α(y) ψ_β(y)`, `p_α = (λ_α − z₁^{σ₁})⁻¹` | `Im z₁, Im z₂ > 0`, `3 ≤ L` | exact (script: diffs `≤ 1.4e-16`, all 4 sign pairs) |
| 9 | block bound | `\|M_{αβ}\| ≤ N ∑_x (S_{xy}+N⁻¹)\|ψ_α(x)\|\|ψ_β(x)\|`, `∑_x (S_{xy}+N⁻¹) = 2` | `svarF ≥ 0`, column sum 1 (`3 ≤ L`) | no `d` enters; `\|M\| ≤ 2N` (`blockM2_le_432` at `N=216`) |
| 10 | `Ag` (target 4a) | `θ/2(q₁Nq₂+Nq₁q₂) + 2N(o₁q₂+q₁o₂)`, `q_i = ηt Cb/(Im u_i)²`, `o_i = Cb(8/w'+8ηt/w'²) + ((2^{K'}w')²)⁻¹` | `Ag ≥` this | dyadic shells give `4/(2^k w') + 4η/(4^k w'²)`, sums `8/w'` and `16η/(3w'²) ≤ 8ηt/w'²` (slack factor `3/2` in the 2nd term) |
| 11 | `Ab` (target 4a, `Bad` block) | `4N q₁ q₂` (`θ=0`, `o_i=q_i`) | `Ab ≥ 4Nq₁q₂` | exact |
| 12 | crude (4b) | `4 (Im u₁)⁻²(Im u₂)⁻²` from `A_y ≤ 4N q₁q₂`, `q_i = (Im u_i)⁻²` | none | exact |
| 13 | `d` and `L,W` relations | `d` enters only through `Idx`, `Zd`, `scirc`, `SBR`, `card_Idx`, `2d+1`; no `3 ≤ d` | `3 ≤ L`, `1 ≤ W`; `(eq:WO)` only in target 3 | none beyond rows 4-5 |

Not-pins: no pin is stated or proved; `UNUyw` integrand (`Pins.lean:712-716`) and the left side of 4a/4b are token-identical
(`(G*G) x y * scirc x y * (G*G) y x`, `Gres`, `scirc d L W lam`); target 3 hypotheses are those of `UNOUQUE` (`Pins.lean:637-643`).

### (ii) One concrete nondegenerate instance

`d=3, L=3, W=2, N=216` (`Idx 3 3 2`, 27 blocks), `lam = 1/2` (targets 1,2,4; `lam = 1` in target 3), `𝔡 = 1/10`, `E = 0`.
Targets 4a/4b: `H = 1`, `s = {0}`, `w 0 = u₁ = u₂ = I`, `ηt = Cb = w' = 1`, `K' = 1`, `Bad ≡ False`, `θ = 2N = 432`.
Hypotheses: `Im = 1 ≤ ηt`; `jakGridGood H 1 1 E₀ r` since `Im (1−x−i)⁻¹ = 1/((1−x)²+1) ≤ 1 = Cb`
(`JakKernelInst.gridGood_one`); `hBad` from `‖M‖ ≤ 2N = 432` (row 9); `hAg`: `θ/2·(216+216) = 93312`,
`o = 16 + 1/4 = 16.25`, `2N·2·o = 14040`, `Ag = 107352` (equality); `hAb`: `Ab = 4·216 = 864`.
Target 3: `P = dirac`, `Hr ≡ 1`, `p = 1` (so `hp` is `prob_le_one`), `a₀ = 0`; `hlam`: `2^{-3/2+1/10} = 0.3789 ≤ lam = 1`; `1 ≤ W = 2`; `0 < 𝔡`; `3 ≤ L`.
External hypothesis: only `hp` (the per-block `queBadMat` bound, a plain hypothesis, not a registered pin, not an `∀ᶠ` statement);
at the instance it is discharged by `p = 1`. Consumer value `p = queBound = W^{-𝔡/15+τ}` (`un_que_exponent`) is UN-23's; no limit is used in this file.
Remark: at `p = 1` the conclusion of `inst_bad2` (`≤ 7`) is implied by `dirac ≤ 1`; that is the instance as pinned by the check.

Command (Python, scratch only): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2271/pre.py`
(random Hermitian `H`, `N=216`, `d=3, L=3, W=2, lam=1/2`; `ψ_α` = columns of `eigh`; blocks `blk(i)=(i_k // W) mod L`; `SBR` from `sbKernelR`,
`Gres H z σ = (H − z^σ)⁻¹`, `z^σ = z` or `conj z`):
```
row sums SBR: 0.9999999999999999 1.0000000000000002  support per row: {np.int64(7)}  2d+1 = 7
N = 216
1b y=0 a=0 b=0  lhs=(-0.2394632857+0j) rhs=(-0.2394632857+0j) |diff|=5.55e-16
1b y=37 a=5 b=100  lhs=(0.0401392281-0.008864993j) rhs=(0.0401392281-0.008864993j) |diff|=1.39e-16
1b y=200 a=17 b=20  lhs=(0.0515151047+0.0945225172j) rhs=(0.0515151047+0.0945225172j) |diff|=1.55e-17
1a max|diag M2 - blockM| = 2.22e-16
2 (s1,s2)=(1,1) lhs=(0.0150879096+0.0080593363j) rhs=(0.0150879096+0.0080593363j) |diff|=5.20e-18
   4b (s=emptyset): |y-term| = 0.0171055 <= 100 : True
2 (s1,s2)=(1,0) lhs=(0.0126012631+0.0065826563j) rhs=(0.0126012631+0.0065826563j) |diff|=1.39e-16
   4b (s=emptyset): |y-term| = 0.014217 <= 100 : True
2 (s1,s2)=(0,1) lhs=(0.009649634-0.0100208496j) rhs=(0.009649634-0.0100208496j) |diff|=2.02e-17
   4b (s=emptyset): |y-term| = 0.0139116 <= 100 : True
2 (s1,s2)=(0,0) lhs=(0.0159262214-0.0035040607j) rhs=(0.0159262214-0.0035040607j) |diff|=7.82e-17
   4b (s=emptyset): |y-term| = 0.0163071 <= 100 : True
3 |supp| = 7 ; max|M2| = 0.5276 <= max_b max|u_b| = 1.5229 : True
blockM2_le_432: max over a0,alpha,beta of |M2| = 0.606 <= 2N = 432
N=216 theta=432 o=16.25 Ag=107352.0 Ab=864.0  Ag/N=497.000
hlam: 2^(-3/2+1/10) = 0.3789 <= lam=1; window slack 2^(1/30)=1.0234
H=1 (s1,s2)=(1,1): Im m * |T| = 0.005671 ; 4a rhs = 497.0000 ; 4b rhs = 4 = 4.0
H=1 (s1,s2)=(1,0): Im m * |T| = 0.005671 ; 4a rhs = 497.0000 ; 4b rhs = 4 = 4.0
H=1 (s1,s2)=(0,1): Im m * |T| = 0.005671 ; 4a rhs = 497.0000 ; 4b rhs = 4 = 4.0
H=1 (s1,s2)=(0,0): Im m * |T| = 0.005671 ; 4a rhs = 497.0000 ; 4b rhs = 4 = 4.0
```
(`4b` lines: `s = ∅`, `u₁ = 0.3+0.5i`, `u₂ = −0.2+0.4i`, bound `4/(0.25·0.16) = 100`. The `H = 1` lines: `Im m(I) = 1/2`, `|T| = 0.01134`; 4a/4b right sides `497`, `4`.)

### Verdict per target
- 1 (`blockM2`, `blockM2_self`, `blockM2_eq`): PASS (identity of rows 3, 6; script check 1a/1b).
- 2 (`green_spectral_identity_blockM2`): PASS (row 8; script check, all four `(σ₁,σ₂)`).
- 3 (`measure_bad2_le_of_queBadMat`): PASS (rows 1, 2, 4-7; hypotheses of the merged one-index form; support `7 = 2d+1` at `d=3, L=3`).
- 4a (`uyw_pointwise_good`): PASS (rows 9-11; constants close with equality at the instance, `Ag = 107352`, `Ab = 864`).
- 4b (`uyw_pointwise_crude`): PASS (row 12).
- 5 (`UywKernelInst` instances): PASS (instance above has every hypothesis satisfied, `N = 216`, nonempty).

## (b) Script output (stage 1b, written Tue Oct  6 08:39:25 UTC 2026)

No (a′) correction needed (no mistake found in section (a)).  Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2271`; `scratch/` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2271/`.
```
$ git log --format='%h %s' main..t/T2271 ; git diff --stat main...t/T2271
4f0ce83 T2271: module doc line width, linter options after the doc
2c2c971 T2271: rename extra instance inst_identity to inst_identity2 (avoid JakSpectralInst name)
1342879 T2271: UN-22 Universality/UywKernel (pair kernel layer of (uywy7723r3rf))
 RBM3D/Universality/UywKernel.lean | 1470 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1470 insertions(+)
$ lake build RBM3D.Universality.UywKernel > build.out ; echo exit=$? ; tail -1 build.out ; grep -n "UywKernel.lean" build.out | grep -v "info:" | wc -l
exit=0
Build completed successfully (3331 jobs).
0     (no warning or error line from UywKernel.lean)
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/UywKernel.lean ; wc -l RBM3D/Universality/UywKernel.lean
(no output)
1470 RBM3D/Universality/UywKernel.lean
$ lake build   (full library, root RBM3D.lean at f515695, cached)   -> exit=0, last line: Build completed successfully (4077 jobs).
```
`#print axioms` lines printed by the build (file line `:0:`, names `RBM.Univ.`-stripped by `sed`):
```
1456:0: 'blockM2_self' depends on axioms: [propext, Classical.choice, Quot.sound]
1457:0: 'blockM2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
1458:0: 'green_spectral_identity_blockM2' depends on axioms: [propext, Classical.choice, Quot.sound]
1459:0: 'measure_bad2_le_of_queBadMat' depends on axioms: [propext, Classical.choice, Quot.sound]
1460:0: 'uyw_pointwise_good' depends on axioms: [propext, Classical.choice, Quot.sound]
1461:0: 'uyw_pointwise_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
1462:0: 'UywKernelInst.blockM2_le_432' depends on axioms: [propext, Classical.choice, Quot.sound]
1463:0: 'UywKernelInst.inst_self' depends on axioms: [propext, Classical.choice, Quot.sound]
1464:0: 'UywKernelInst.inst_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
1465:0: 'UywKernelInst.inst_identity2' depends on axioms: [propext, Classical.choice, Quot.sound]
1466:0: 'UywKernelInst.inst_bad2' depends on axioms: [propext, Classical.choice, Quot.sound]
1467:0: 'UywKernelInst.inst_good' depends on axioms: [propext, Classical.choice, Quot.sound]
1468:0: 'UywKernelInst.inst_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Target statements, extracted by `python3 scratch/extract.py <names> | grep -v '^$'` (declaration line up to `:=`):
```
noncomputable def blockM2 (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (a0 : Zd d L) (α β : Idx d L W) : ℂ :=
theorem blockM2_self {d L W : ℕ} [NeZero L] [NeZero W] (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (a0 : Zd d L) (α : Idx d L W) :
    blockM2 d L W lam hH a0 α α = blockM d L W lam hH a0 α := by
theorem blockM2_eq (hL : 3 ≤ L) (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (y α β : Idx d L W) :
    blockM2 d L W lam hH (siteBlock d L W y) α β =
      (((W * L) ^ d : ℕ) : ℂ) *
        ∑ x, (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis β x)) * scirc d L W lam x y := by
theorem green_spectral_identity_blockM2 (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (y : Idx d L W) (z₁ z₂ : ℂ)
    (hη₁ : 0 < z₁.im) (hη₂ : 0 < z₂.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx d L W, (Gres H z₁ σ₁ * Gres H z₁ σ₁) x y * scirc d L W lam x y *
        (Gres H z₂ σ₂ * Gres H z₂ σ₂) y x) =
      ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * ∑ α : Idx d L W, ∑ β : Idx d L W,
        spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α *
          (spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β) *
            blockM2 d L W lam hH (siteBlock d L W y) α β *
              star (hH.eigenvectorBasis α y) * hH.eigenvectorBasis β y := by
theorem measure_bad2_le_of_queBadMat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hL : 3 ≤ L) {lam 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (a0 : Zd d L)
    {Hr : Ω → Matrix (Idx d L W) (Idx d L W) ℂ} (hH : ∀ ω, (Hr ω).IsHermitian) (p : ℝ≥0∞)
    (hp : ∀ b : Zd d L, P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤ p) :
    P {ω | ∃ α β, |(hH ω).eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        |(hH ω).eigenvalues β - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM2 d L W lam (hH ω) a0 α β‖} ≤
      ((2 * d + 1 : ℕ) : ℝ≥0∞) * p := by
theorem uyw_pointwise_good (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (m : ℕ) (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) (ηt Cb w' θ Ag Ab : ℝ)
    (hη₁ : 0 < u₁.im) (hη₁' : u₁.im ≤ ηt) (hη₂ : 0 < u₂.im) (hη₂' : u₂.im ≤ ηt)
    (hηw : ∀ j, 0 < (w j).im) (hηw' : ∀ j, (w j).im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hθ : 0 ≤ θ) (K' : ℕ)
    (hG1 : ∀ k ≤ K', jakGridGood H ηt Cb u₁.re (2 ^ k * w'))
    (hG2 : ∀ k ≤ K', jakGridGood H ηt Cb u₂.re (2 ^ k * w'))
    (hG3 : jakGridGood H ηt Cb u₁.re 0) (hG4 : jakGridGood H ηt Cb u₂.re 0)
    (hG5 : ∀ j, jakGridGood H ηt Cb (w j).re 0)
    (Bad : Zd d L → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' →
      |hH.eigenvalues β - u₂.re| ≤ w' → ‖blockM2 d L W lam hH a0 α β‖ ≤ θ)
    (hAg : θ / 2 * ((ηt / u₁.im ^ 2 * Cb) * ((((W * L) ^ d : ℕ) : ℝ) * (ηt / u₂.im ^ 2 * Cb)) +
        ((((W * L) ^ d : ℕ) : ℝ) * (ηt / u₁.im ^ 2 * Cb)) * (ηt / u₂.im ^ 2 * Cb)) +
      2 * (((W * L) ^ d : ℕ) : ℝ) *
        ((Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹) * (ηt / u₂.im ^ 2 * Cb) +
          (ηt / u₁.im ^ 2 * Cb) * (Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹)) ≤
      Ag)
    (hAb : 4 * (((W * L) ^ d : ℕ) : ℝ) * ((ηt / u₁.im ^ 2 * Cb) * (ηt / u₂.im ^ 2 * Cb)) ≤ Ab)
    (y : Idx d L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
          (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ ≤
      (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ((((W * L) ^ d : ℕ) : ℝ)⁻¹ *
          (Ag + (if Bad (siteBlock d L W y) then Ab else 0))) := by
theorem uyw_pointwise_crude (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (m : ℕ) (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) (hη₁ : 0 < u₁.im) (hη₂ : 0 < u₂.im)
    (hηw : ∀ j, 0 < (w j).im) (y : Idx d L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
          (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ ≤
      (∏ j ∈ s, (w j).im⁻¹) * (4 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2)) := by
```
Compiled nonempty instances (same extraction; namespace `RBM.Univ.UywKernelInst`, `d = 3`, `L = 3`, `W = 2`, `N = 216`; the instances apply the targets at the preflight data; `blockM2_le_432` is the helper bound used for `θ`):
```
theorem blockM2_le_432 {H : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hH : H.IsHermitian) (lam : ℝ)
    (a0 : Zd 3 3) (α β : Idx 3 3 2) : ‖blockM2 3 3 2 lam hH a0 α β‖ ≤ 432 := by
theorem inst_self :
    ∀ hH : H1.IsHermitian,
    blockM2 3 3 2 (1 / 2) hH 0 y0 y0 = blockM 3 3 2 (1 / 2) hH 0 y0 :=
theorem inst_eq :
    ∀ hH : H1.IsHermitian,
    blockM2 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) y0 y1 =
      (((2 * 3) ^ 3 : ℕ) : ℂ) *
        ∑ x, (hH.eigenvectorBasis y0 x * star (hH.eigenvectorBasis y1 x)) * scirc 3 3 2 (1 / 2) x y0 :=
theorem inst_identity2 :
    ∀ hH : H1.IsHermitian,
    (∑ x, (Gres H1 Complex.I true * Gres H1 Complex.I true) x y0 * scirc 3 3 2 (1 / 2) x y0 *
        (Gres H1 Complex.I false * Gres H1 Complex.I false) y0 x) =
      ((((2 * 3) ^ 3 : ℕ) : ℂ))⁻¹ * ∑ α, ∑ β,
        spectralGsigPole hH Complex.I true α * spectralGsigPole hH Complex.I true α *
          (spectralGsigPole hH Complex.I false β * spectralGsigPole hH Complex.I false β) *
            blockM2 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) α β *
              star (hH.eigenvectorBasis α y0) * hH.eigenvectorBasis β y0 :=
theorem inst_bad2 :
    ∀ hH : ∀ _ω : Unit, H1.IsHermitian,
    (Measure.dirac ()) {ω : Unit | ∃ α β,
        |(hH ω).eigenvalues α - 0| ≤ (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
        |(hH ω).eigenvalues β - 0| ≤ (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
        ((2 : ℕ) : ℝ) ^ (-((1 / 10 : ℝ) / 6)) ≤ ‖blockM2 3 3 2 1 (hH ω) 0 α β‖} ≤
      ((2 * 3 + 1 : ℕ) : ℝ≥0∞) * 1 := by
theorem inst_good (y : Idx 3 3 2) (σ₁ σ₂ : Bool) :
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN H1 Complex.I).im) *
        ‖∑ x, (Gres H1 Complex.I σ₁ * Gres H1 Complex.I σ₁) x y *
          scirc 3 3 2 (1 / 2) x y * (Gres H1 Complex.I σ₂ * Gres H1 Complex.I σ₂) y x‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), (1 / Complex.I.im * 1)) *
        ((((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * (107352 + (if False then (864 : ℝ) else 0))) :=
theorem inst_crude (σ₁ σ₂ : Bool) :
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN H1 Complex.I).im) *
        ‖∑ x, (Gres H1 Complex.I σ₁ * Gres H1 Complex.I σ₁) x y0 *
          scirc 3 3 2 (1 / 2) x y0 *
            (Gres H1 Complex.I σ₂ * Gres H1 Complex.I σ₂) y0 x‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), Complex.I.im⁻¹) *
        (4 * ((Complex.I.im⁻¹) ^ 2 * (Complex.I.im⁻¹) ^ 2)) :=
```
Proof terms (abridged): `inst_good := uyw_pointwise_good (d := 3) (L := 3) (W := 2) (by norm_num) (1 / 2) H1_herm 1 {0} (fun _ => I) I I 1 1 1 432 107352 864 … (fun _ : Zd 3 3 => False) (fun a0 _ α β _ _ => blockM2_le_432 H1_herm _ a0 α β) (by norm_num) (by norm_num) y σ₁ σ₂` (grids by `JakKernelInst.gridGood_one`); `inst_crude := uyw_pointwise_crude …`; `inst_bad2` applies `measure_bad2_le_of_queBadMat (Measure.dirac ()) … (lam := 1) (𝔡 := 1 / 10) (E := 0) … 0 hH 1 (fun b => prob_le_one)` and discharges `hlam` by `Real.rpow_le_one_of_one_le_of_nonpos`.  Two `example`s apply 4a, 4b at the non-scalar `H2 = diag(x₀.val)`.

Check file against the library (`scratch/T2271Scratch.lean` = the check's sections 2.2-2.5 with `import RBM3D.Universality.UywKernel`, the check's own `blockM2` removed so that `RBM.Univ.blockM2` is used, plus `example : T2271_X := X` for the six targets and `blockM2_le_432`, `inst_self`, `inst_bad2`, `inst_good`, `inst_crude`):
```
$ lake env lean scratch/T2271Scratch.lean > scratch.out ; echo exit=$? ; grep -c error scratch.out ; grep -c '^example' scratch/T2271Scratch.lean
exit=0
0
11
$ python3 (whitespace-normalised text of the check's `noncomputable def blockM2` vs the file's)   ->   vocabulary 2.1 identical: True
```
Consumer token check (`lake env lean scratch/TokenCheck.lean`, exit 0, empty output): `uyw_pointwise_crude` and `uyw_pointwise_good` at `H = ouMat (UNModel.band sz) n t ω`, `lam = sz.lam n` have the integrand of `UNUyw` (`Pins.lean:712-716`) token for token; `uyw_pointwise_crude` at `ouMatC (K.M sz)`, `lam = K.lamV sz n` has that of `UNUywk` (`PinsK.lean:378`); `measure_bad2_le_of_queBadMat` at `P = ouP (UNModel.band sz) n`, `Hr = ouMat …`, `queBadMat … (𝔡 / 3) (𝔡 / 6) E b` takes the `UNOUQUE` event (`Pins.lean:637-643`) as `hp`.

Registry pre-check (§20 (2)): `printf 'import RBM3D\nimport RBM3D.Universality.UywKernel\n\n#assert_rbm_axioms\n' > RegPrecheck.lean ; lake env lean RegPrecheck.lean > regpre.out` (the same file without the second import: regbase.out):
```
exit=0 (both)
$ diff regbase.out regpre.out
1c1
< axiom audit: 7889 theorems, 2608 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 7905 theorems, 2613 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
Owed premises listed: 155 in both; `Test/Axioms.lean` is untouched (the branch diff above lists one file); no registry line added or deleted.

Name-clash grep (`scratch/clash2.sh`):
```
hits outside RBM3D/Universality/UywKernel.lean (grep -rnw --include='*.lean' NAME RBM3D RBM3D.lean):
blockM2=0  blockM2_self=0  blockM2_eq=0  green_spectral_identity_blockM2=0  measure_bad2_le_of_queBadMat=0  uyw_pointwise_good=0  uyw_pointwise_crude=0  UywKernelInst=0  blockM2_le_432=0  inst_self=0  inst_eq=0  inst_identity2=0  inst_bad2=0  UywKernel_=0  UywKernel=0  
declarations of the same short name elsewhere (other namespaces; RBM.Univ.UywKernelInst.* is fresh):
inst_good: Universality/JakKernel.lean  | inst_crude: Universality/JakKernel.lean  | H1: Induction/QDriftA.lean Universality/JakKernel.lean Universality/JakSpectral.lean  | y0: Universality/JakKernel.lean Universality/JakSpectral.lean  | y1:  | H2: Universality/JakKernel.lean  | H1_herm: Universality/JakKernel.lean  | H2_herm: Universality/JakKernel.lean  | 
UywKernelInst hits elsewhere: 0;  file on main: 0
```
Ports: RBM2D `Universality/UywKernel.lean` at `c9a24cf` (`git show c9a24cf:RBM2D/Universality/UywKernel.lean`, 1372 lines); no RBM1D file was read or copied by this ticket (the RBM1D citations in docstrings come with the copied text).  First line below is RBM2D HEAD (`log -1 --format=%h`), then the diff-stat of the source file since `c9a24cf`:
```
9e0f275
 RBM2D/Universality/UywKernel.lean | 334 ++++++--------------------------------
 1 file changed, 51 insertions(+), 283 deletions(-)
```
RBM2D `:369-509` (Q rows; `RBM.green` -> `Gres · · true`, `RBM.im_green_apply_self` -> `im_Gres_apply_self`), `:513-692` (pair combinatorics, verbatim), `:840-893` (target 2), `:965-1163` (A_y row, pointwise bounds; `Gsig ^ 2` -> `Gres * Gres`, `Scirc/Spaper` -> `scirc/svarF`), `:1165-1363` (instances); replaced, not ported: `:757-767` (`blockM2`), `:800-828` (`blockM2_eq`), `:909-961` (target 3).  Copied with prefix rename `JakKernel_` -> `UywKernel_` from merged `RBM3D/Universality/JakKernel.lean` at f515695 (private there, not callable): `:171-191, 247-400, 404-472, 621-675`; from merged `JakSpectral.lean`: `:56-65, 79-121`.

Narrative.
- New proofs (no merged template): `UywKernel_sum_svarF_group` (block partition of `∑_x f(x) S_{xy}`, template `unMy_eq` `Pins.lean:1156`) and `blockM2_eq` (`S = W^{-d} SBR`, `∑_b SBR(b,[y]) = 1`, orthonormality `∑_x conj ψ_β ψ_α = δ_{αβ}` cancels the `-N⁻¹` part of `scirc`; `blockM2` has `conj ψ_β · ψ_α`, the right side `ψ_α · conj ψ_β`); `UywKernel_bad2_subset` (averaging step: weights `SBR b a₀ ≥ 0` with sum `1`, so some block of positive weight has `‖u_b‖ ≥ W^{-𝔡/6}`; it is a `queBadMat` failure at `(i, j) = (β, α)`; window by `un_window_sub`, threshold `W^{d-𝔡/6}/N`); the union bound over `≤ 2d + 1` blocks uses `unBadY_card_le`.
- Statements: the six targets and `blockM2` are the check's text; differences: binder names and `Ω : Type*` (check: `Type`).  No `3 ≤ d` hypothesis; `d` enters only through `Idx`, `Zd`, `scirc`, `SBR`, `card_Idx`, `2d + 1`.
- Beyond the pinned instances: `inst_eq` (target 1b), `inst_identity2` (target 2) at `H1`, `lam = 1/2`; the helpers `y1`, `H2`, `H1_herm`, `H2_herm` are public in `RBM.Univ.UywKernelInst` (file-stem namespace, as `JakKernelInst`).  `inst_bad2` uses `p = 1` as pinned, so its conclusion `≤ 7` also follows from `dirac ≤ 1`; what it checks is that every deterministic hypothesis of target 3 holds at the data.
- Not targets (as ticket): no pin proved or stated (`UNUyw`, `UNJakUywRow`, `UNUywk`, `UNJakUywRowk`, `UNJakUywRowBA` stay owed), no merged file touched, `RBM.green`, `Gsig`, `Spaper`, `Epaper`, `sbSupport` not added.  Size 1470 lines (ticket estimate 1200 / 1350 / 1480; the stop rule at 1500 was not reached).
- Root import: the hub adds `import RBM3D.Universality.UywKernel` after the last `import` line of `RBM3D.lean` at merge.

## (c) Verified Mathlib names (`#check` of each; `lake env lean scratch/MathlibNames.lean`: exit 0, 0 errors, 25 `#check` lines)
`Finset.sum_fiberwise`, `Finset.sum_lt_sum`, `Finset.sum_sub_distrib`, `Finset.sum_range_succ`, `Finset.single_le_sum`, `Finset.prod_le_prod₀`
`Matrix.isHermitian_one`, `Matrix.isHermitian_diagonal_iff`, `Matrix.diagonal_mul_diagonal`
`MeasureTheory.measure_mono`, `MeasureTheory.measure_biUnion_finset_le`, `MeasureTheory.prob_le_one`
`Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_natCast`, `Real.rpow_add`, `sum_geometric_two_le`
`eq_inv_mul_iff_mul_eq₀`, `div_le_iff₀`, `inv_anti₀`, `pow_le_pow_left₀`, `norm_sum_le`, `Complex.norm_real`, `Complex.norm_natCast`, `Complex.abs_im_le_norm`, `Complex.abs_re_le_norm`
Names verified absent: none looked up.

## (d) Open issues and paper-delta candidates
- **T2271a** (design table, no paper statement; as the ticket): portmap row UN-22 (`T2162-portmap.md:216`) estimate 1170 lines -> file 1470 lines (the `Gres` decomposition copy, the `svarF` copies, the new `SBR` proofs of `blockM2_eq` and of the averaging step); the pair moment `blockM2` is the `2d+1`-weight form with `δ_{αβ}` (RBM2D: `1/5` average with `ψ_β^*ψ_α`).
- No T2271b: no statement difference between the ticket's pins and the file was found.
- Open: none.  Hand-off to UN-23 (`Uyw`): `uyw_pointwise_good` (4a), `uyw_pointwise_crude` (4b), `blockM2`, `measure_bad2_le_of_queBadMat` (target 3, `hp` from `UNOUQUE`); the shift `u.re` vs `E` is UN-23's.
