Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 04:06:37 UTC 2026

### (i) Exponent table

Data: `N = (W L)^d`, `S_xy = svarF d L W lam x y = W^{-d} SBR d L lam (split x).1 (split y).1`, `S°_xy = S_xy - N⁻¹`,
`M_{y,α} = N ∑_x |ψ_α(x)|² S°_xy` (= `blockM`, = merged `unMy`), `p_α = (λ_α - z_σ)⁻¹`, `z_σ = z` (σ = true) or `z̄` (σ = false).
Source lines read: `docs/tickets/checks/T2251-check.lean` (sections 2.1-2.7), `RBM3D/Universality/Pins.lean:612, 694-703, 1140-1355`,
`RBM3D/Defs/Block.lean:74-90`, `RBM3D/Propagator/Gap.lean:206-232`, `RBM3D/Gauss/FineModel.lean:47-56`.

| Quantity / threshold | Value | Constraint (target) | Slack |
|---|---|---|---|
| `3 ≤ L` (targets 2-5) | instance `L = 3` | used only through `sum_SBR_row` (`Gap.lean:206`; `∑_b SBR a b = 1`, kernel mass `a + 2d·b = 1` via `card_nbhd`); `SBR_comm` for columns | 0 (tight, allowed: `L = 3` has `2d = 6` distinct neighbours) |
| `d` | `3` | enters only via `Idx d L W`, `Zd d L`, `svarF`, `SBR`, `2d+1`; no `3 ≤ d` hypothesis in any target | n/a |
| `W ≥ 1` (5b only) | `W = 2` | `1 ≤ (W:ℝ)` (`unBadY_measure_le`, `un_window_sub`) | `1` |
| `lam` (targets 2-4) | `1/2` | any real: `sbKernelR_nonneg` holds for every `g` (`Block.lean:88`, `1 + 2dg² > 0`); `sum_sbKernelR` needs only `3 ≤ L` (`Block.lean:93`, comment: "No sign condition on `g` is needed") | none needed |
| `hlam` (5b): `W^{-d/2+𝔡} ≤ lam` | `2^{-3/2+1/10} = 0.378929 ≤ lam = 1` | (eq:WO) window inclusion `un_window_sub` (`Pins.lean:908`) | `0.6211` |
| `𝔡` (5a, 5b) | `1/10` | `0 < 𝔡` | `1/10` |
| QUE params `ε₀ = 𝔡/3`, `c = 𝔡/6` | `1/30`, `1/60` | `0<ε₀<𝔡/2`, `0<c<min(ε₀, 𝔡/5)` (`un_que_params`) | `ε₀ < 𝔡/2`: `1/15`; `c < ε₀`: `1/60`; `c < 𝔡/5`: `1/300` |
| window of `UNBadY`/5a | `\|λ_α - E\| ≤ N⁻¹ W^{𝔡/3}` | token-equal to `Pins.lean:1149` | `W^{𝔡/3}/N = 0.0047378` at the instance |
| threshold `θ` of `UNBadY`/5a | `W^{-𝔡/6} ≤ ‖blockM‖` | token-equal to `Pins.lean:1150` after `‖blockM‖ = \|unMy\|` (`blockM_eq_unMy`, `‖(r:ℂ)‖ = \|r\|`) | `θ = 0.98851` at the instance |
| union count (5b) | `2d + 1 = 7` | `unBadY_card_le` (`Pins.lean:1298`); `((2d+1:ℕ):ℝ≥0∞) * p` as in `unBadY_measure_le` | `\|supp\| = 7` attained at `L = 3`: slack 0 (true count) |
| mass constant (4) | `2N = 432` | `∑_α\|M_α\| ≤ N ∑_x \|S°_xy\| ≤ N ∑_x (S_xy + N⁻¹) = N(1 + 1)`; uses `∑_α\|ψ_α(x)\|² = 1`, `∑_x S_xy = 1`, `S_xy ≥ 0` | actual max over `a₀` at the random instance `28.9956` (factor 14.9) |
| column sum `∑_x S_xy` | `1` | `card_Iblk`: `W^{-d}·W^d ∑_b SBR b a = 1` | 0 (identity) |
| spectral poles | `Im z_σ = ±Im z ≠ 0` | `0 < z.im ⇒ ∀α, (λ_α:ℂ) ≠ z_σ` (λ real); `‖p_α(z)‖ = ‖p_α(z̄)‖` (1d) | `Im z = 1` at the instance |
| `Gres H w true = (H - w)⁻¹` (1a) | needs `∀α, λ_α ≠ w` | `Ring.inverse` = `inv` since `H - w` is a unit (`isUnit_sub_smul_of_isHermitian`, `Resolvent.lean:132`) | n/a |

Mathematical statements as used (all checked against the file text, not restated beyond need):
- 1a-1c: `(H - w)⁻¹ = U diag(p) U*`, `U_{xα} = ψ_α(x)`, so `(G²)_{xx} = ∑_α p_α² |ψ_α(x)|²`, `G_{yy} = ∑_β p_β |ψ_β(y)|²` (σ = false: pole `(λ - z̄)⁻¹`, as in `Gres`, `GLoopFlow.lean:74`).
- 2a: unit vector `∑_x‖ψ_α x‖² = 1` from `IsOrthoEigenbasis` (`.1 α α`), then `unMy_eq` (`Pins.lean:1156`) gives the `SBR`-weighted block form; `scirc = ↑svarF - N⁻¹` (`Pins.lean:612`) gives 2a/2b. Weights `SBR b a₀ ≥ 0`, sum 1; `blockM` coefficient `N/W^d ∑_{x∈[b]} star ψ ψ - 1` is the merged `queBadMat` overlap minus `W^d/N` scaled by `N/W^d` (`Pins.lean:392-397`).
- 3a: `∑_x (G₁²)_{xx} S°_xy (G₂)_{yy} = ∑_{α,γ} p_α² q_γ |ψ_γ(y)|² ∑_x |ψ_α(x)|² S°_xy = N⁻¹ ∑_{α,γ} p_α² q_γ M_{y,α} |ψ_γ(y)|²`; 3b: triangle inequality on the right side.
- 5a: `μ = hH.eigenvalues`, `ψ = hH.eigenvectorBasis` witness `UNBadY` (`IsOrthoEigenbasis` from 1e). 5b: `{∃α …} ⊆ {UNBadY …}` (5a) then `unBadY_measure_le` (`Pins.lean:1320`) with the same hypotheses `3 ≤ L`, `1 ≤ W`, `0 < 𝔡`, `hlam`, `hp` (the statement of 5b equals that of `unBadY_measure_le` after the inclusion).
- Consumer token check (read, `Pins.lean:700-703`, `PinsK.lean:370-373`): `UNJak`/`UNJakk` integrand `∑ x, (Gres M z b₁ * Gres M z b₁) x x * scirc d (sz.L n) (sz.W n) (sz.lam n | K.lamV sz n) x y * Gres M z b₂ y y` has the same shape (`Gres`, `scirc`, arguments in the same order) as the left side of 3a/3b at `Hm = ouMat …/ouMatC …`, `lam = sz.lam n / K.lamV sz n`; `0 < Im (z i)` from `InWindow` (`Pins.lean:501`, `N^{-1-τU} ≤ Im z`, `rpow_pos`).

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 3`, `W = 2` (`N = 216`, `W L = 6`), `lam = 1/2` (targets 1-4) and `lam = 1` (5b), `z = 0.3 + 0.5i` (Python; Lean instances use `z = I`),
`y = 0`, `a₀ = block(0)`, random Hermitian `H` (216×216) for the numerical check; Lean instances use `H = 1`, `𝔡 = 1/10`, `E = 1`, `p = 1`,
`P = δ_()` on `Unit` (a probability measure, so `hp: δ(·) ≤ 1` holds). Every hypothesis of every target holds: `3 ≤ 3`, `0 < Im z`, `1 ≤ 2`, `0 < 1/10`, `hlam: 0.3789 ≤ 1`. No `N = 0`, no empty index, no collapsed window (window `0.0047` around `E`, `7` blocks in the support).

Command (script at `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2251/inst.py`; numpy 2.0.2; builds `SBR` from `sbKernelR` with the `ℓ¹` periodic distance `zdistD`, blocks `(i // W) mod L`):

```
python3 inst.py
SBR row sums==1: True col: True support<=2d+1: 7 min entry>=0: True
N = 216 col sums of S ==1: True
Hermitian: True orthonormal: True
max|blockM - unMy| (blockM_eq, blockM_eq_unMy): 2.4216739724636227e-15
sigma True 1b err 2.299696420679771e-15 1c err 4.359039439065041e-15
sigma False 1b err 2.1715079727778364e-15 1c err 3.9751566016584044e-15
1a err (w=z): 4.359039439065041e-15
3a s1=True s2=True |lhs-rhs|=9.50e-17 rel=6.96e-15; 3b |lhs|=1.3642e-02 <= 2.9562e-01: True
3a s1=True s2=False |lhs-rhs|=1.33e-16 rel=9.73e-15; 3b |lhs|=1.3642e-02 <= 2.9562e-01: True
3a s1=False s2=True |lhs-rhs|=3.54e-16 rel=2.59e-14; 3b |lhs|=1.3642e-02 <= 2.9562e-01: True
3a s1=False s2=False |lhs-rhs|=3.52e-16 rel=2.58e-14; 3b |lhs|=1.3642e-02 <= 2.9562e-01: True
pole norm eq (1d): True
mass: max_a0 sum_alpha|M| = 28.99562500256506  <= 2N = 432 : True
hlam: W^(-d/2+dd)= 0.37892914162759955 <= lam= 1.0 : True ; 1<=W: True ; 0<dd: True
window N^-1 W^(dd/3)= 0.004737842092577662 ; threshold W^(-dd/6)= 0.9885140203528962 ; 2d+1 = 7
eps0=dd/3 in (0,dd/2): True c=dd/6<min(dd/3,dd/5): True slacks: 0.016666666666666666 0.003333333333333334
H=1, lam=1: |eigenvalue-E| max = 0.0 ; max|blockM| = 2.857142857142857
```

External hypotheses: none. The only non-deterministic premise of 5b, `∀ b, P{queBadMat …} ≤ p`, is a hypothesis of the merged `unBadY_measure_le` (`Pins.lean:1320`) and is discharged at `p = 1` by `prob_le_one` for the Dirac measure; no limit statement is assumed (no `∀ᶠ n`, §29 (4) n/a).

Pre-release check: `docs/queue/CONTROL.md:28`: `lake env lean docs/tickets/checks/T2251-check.lean`: exit 0, no error lines.

### Verdicts

- Target 1 (`Gres_sq_apply_self`, `Gres_apply_self_spectral`, `Gres_sq_apply_self_spectral`, `spectralGsigPole_norm_eq_spectralPole`, `isOrthoEigenbasis_eigenvectorBasis`): PASS (finite-dimensional spectral theorem, hypotheses satisfiable; numerics at machine precision).
- Target 2 (`blockM_eq`, `blockM_eq_unMy`): PASS (identity from merged `unMy_eq`; numerics `2.4e-15`).
- Target 3 (`green_spectral_identity_blockM`, `norm_green_spectral_identity_blockM_le`): PASS (identity `rel ≤ 3e-14`, bound holds with slack factor 21.7 at the instance).
- Target 4 (`sum_norm_blockM_le`): PASS (`2N = 432` against `28.996`; proof route as in table).
- Target 5 (`unBadY_of_blockM`, `measure_bad_le_of_queBadMat`): PASS (5a by `blockM_eq_unMy` + 1e; 5b by 5a + merged `unBadY_measure_le`, same hypotheses; instance data satisfy `hlam`).
- Target 6 (instances): PASS (all hypotheses concrete: `3 ≤ 3`, `0 < I.im`, `1 ≤ 2`, `0 < 1/10`, `2^{-1.4} ≤ 1`, `δ ≤ 1`).

Overall verdict: PASS.

## (b) Script output — Tue Oct  6 04:15:43 UTC 2026

### Build
```
$ lake build RBM3D.Universality.JakSpectral   (worktree RBM3D-wt/T2251, branch t/T2251, commit b9e249e)
[exit 0; lines of the output mentioning the new file other than axioms: none (0 warnings from JakSpectral.lean)]
Build completed successfully (3329 jobs).
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" build output
17
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Universality/JakSpectral.lean ; echo $?
1
```

### Axioms of every public declaration (`#print axioms` lines of the file, verbatim)
```
657:0: 'RBM.Univ.Gres_sq_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound]
658:0: 'RBM.Univ.Gres_apply_self_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]
659:0: 'RBM.Univ.Gres_sq_apply_self_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]
660:0: 'RBM.Univ.spectralGsigPole_norm_eq_spectralPole' depends on axioms: [propext, Classical.choice, Quot.sound]
661:0: 'RBM.Univ.isOrthoEigenbasis_eigenvectorBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
662:0: 'RBM.Univ.blockM_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
663:0: 'RBM.Univ.blockM_eq_unMy' depends on axioms: [propext, Classical.choice, Quot.sound]
664:0: 'RBM.Univ.green_spectral_identity_blockM' depends on axioms: [propext, Classical.choice, Quot.sound]
665:0: 'RBM.Univ.norm_green_spectral_identity_blockM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
666:0: 'RBM.Univ.sum_norm_blockM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
667:0: 'RBM.Univ.unBadY_of_blockM' depends on axioms: [propext, Classical.choice, Quot.sound]
668:0: 'RBM.Univ.measure_bad_le_of_queBadMat' depends on axioms: [propext, Classical.choice, Quot.sound]
669:0: 'RBM.Univ.JakSpectralInst.inst_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]
670:0: 'RBM.Univ.JakSpectralInst.inst_block' depends on axioms: [propext, Classical.choice, Quot.sound]
671:0: 'RBM.Univ.JakSpectralInst.inst_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
672:0: 'RBM.Univ.JakSpectralInst.inst_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
673:0: 'RBM.Univ.JakSpectralInst.inst_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Registry pre-check (CLAUDE.md §20 (2)); temporary uncommitted file `import RBM3D` + `import RBM3D.Universality.JakSpectral` + `#assert_rbm_axioms`
```
$ lake env lean RBM3D/PreCheckTmp.lean   -> exit 0 (file removed afterwards; git status: only JakSpectral.lean untracked)
$ diff <(main: import RBM3D + #assert_rbm_axioms) <(with JakSpectral), theorem/definition counts masked
(empty diff: same premise counts and ledgers)
axiom audit: 7470 theorems, 2511 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
axiom audit: 7491 theorems, 2518 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 154 (borrowed 1, owed 102, structural 38, refuted 6, superseded 7).
```

### Target statements (extracted from the file by script; `:=`/`:= by` cut)
```lean
-- JakSpectral.lean:125
theorem Gres_sq_apply_self {H : Matrix n n ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : ∀ α, (hH.eigenvalues α : ℂ) ≠ w) (x : n) :
    (Gres H w true * Gres H w true) x x =
      ∑ α, spectralPole hH w α * spectralPole hH w α *
        (Complex.normSq (hH.eigenvectorBasis α x) : ℂ)
-- JakSpectral.lean:155
theorem Gres_apply_self_spectral {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hη : 0 < z.im) (σ : Bool) (y : n) :
    Gres H z σ y y =
      ∑ β, spectralGsigPole hH z σ β *
        (Complex.normSq (hH.eigenvectorBasis β y) : ℂ)
-- JakSpectral.lean:173
theorem Gres_sq_apply_self_spectral {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hη : 0 < z.im) (σ : Bool) (x : n) :
    (Gres H z σ * Gres H z σ) x x =
      ∑ α, spectralGsigPole hH z σ α * spectralGsigPole hH z σ α *
        (Complex.normSq (hH.eigenvectorBasis α x) : ℂ)
-- JakSpectral.lean:185
theorem spectralGsigPole_norm_eq_spectralPole {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (σ : Bool) (α : n) :
    ‖spectralGsigPole hH z σ α‖ = ‖spectralPole hH z α‖
-- JakSpectral.lean:69
theorem isOrthoEigenbasis_eigenvectorBasis {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    IsOrthoEigenbasis H hH.eigenvalues (fun k x => hH.eigenvectorBasis k x)
-- JakSpectral.lean:268
theorem blockM_eq {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (y α : Idx d L W) :
    blockM d L W lam hH (siteBlock d L W y) α =
      (((W * L) ^ d : ℕ) : ℂ) *
        ∑ x, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) * scirc d L W lam x y
-- JakSpectral.lean:251
theorem blockM_eq_unMy {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (y α : Idx d L W) :
    blockM d L W lam hH (siteBlock d L W y) α =
      ((unMy d L W lam (fun x => hH.eigenvectorBasis α x) y : ℝ) : ℂ)
-- JakSpectral.lean:339
theorem green_spectral_identity_blockM {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (lam : ℝ) {Hm : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : Hm.IsHermitian) (y : Idx d L W)
    {z : ℂ} (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx d L W, (Gres Hm z σ₁ * Gres Hm z σ₁) x x * scirc d L W lam x y *
        Gres Hm z σ₂ y y) =
      ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * ∑ α : Idx d L W, ∑ γ : Idx d L W,
        spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α *
          spectralGsigPole hH z σ₂ γ * blockM d L W lam hH (siteBlock d L W y) α *
          (Complex.normSq (hH.eigenvectorBasis γ y) : ℂ)
-- JakSpectral.lean:357
theorem norm_green_spectral_identity_blockM_le {d L W : ℕ} [NeZero L] [NeZero W]
    (hL : 3 ≤ L) (lam : ℝ) {Hm : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : Hm.IsHermitian)
    (y : Idx d L W) {z : ℂ} (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    ‖∑ x : Idx d L W, (Gres Hm z σ₁ * Gres Hm z σ₁) x x * scirc d L W lam x y *
        Gres Hm z σ₂ y y‖ ≤
      ((((W * L) ^ d : ℕ) : ℝ))⁻¹ *
        (∑ α : Idx d L W, ‖spectralGsigPole hH z σ₁ α‖ ^ 2 *
          ‖blockM d L W lam hH (siteBlock d L W y) α‖) *
        (∑ γ : Idx d L W, ‖spectralGsigPole hH z σ₂ γ‖ *
          Complex.normSq (hH.eigenvectorBasis γ y))
-- JakSpectral.lean:509
theorem sum_norm_blockM_le {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (a0 : Zd d L) :
    ∑ α : Idx d L W, ‖blockM d L W lam hH a0 α‖ ≤ 2 * (((W * L) ^ d : ℕ) : ℝ)
-- JakSpectral.lean:545
theorem unBadY_of_blockM {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    {lam 𝔡 E : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : M.IsHermitian)
    (y α : Idx d L W)
    (h1 : |hH.eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3))
    (h2 : (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM d L W lam hH (siteBlock d L W y) α‖) :
    UNBadY d L W lam 𝔡 E y M
-- JakSpectral.lean:559
theorem measure_bad_le_of_queBadMat {d L W : ℕ} [NeZero L] [NeZero W] {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (hL : 3 ≤ L) {lam 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ))
    (h𝔡 : 0 < 𝔡) (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (y : Idx d L W)
    {Hr : Ω → Matrix (Idx d L W) (Idx d L W) ℂ} (hH : ∀ ω, (Hr ω).IsHermitian) (p : ℝ≥0∞)
    (hp : ∀ b : Zd d L, P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤ p) :
    P {ω | ∃ α, |(hH ω).eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM d L W lam (hH ω) (siteBlock d L W y) α‖} ≤
      ((2 * d + 1 : ℕ) : ℝ≥0∞) * p```

### Statement diff against the check file (sections 2.2-2.7)
Scratch file `scratchpad/T2251/scratch_check.lean` = check sections 2.2-2.7 verbatim (T2251_* defs, library vocabulary) + one `example : T2251_<name> := <name>` per target:
```
$ lake env lean scratch_check.lean ; echo exit $?
exit 0   (17 examples: 12 theorems, 5 instances; no errors, no warnings)
```
Consumer token check (`scratch consumer.lean`, the check's section-3 example proved by `norm_green_spectral_identity_blockM_le (sz.three_le_L n) (sz.lam n) hH y hz b₁ b₂` at `UNModel.band sz`): exit 0 (unused-variable warnings only).

### Compiled nonempty instances (namespace `RBM.Univ.JakSpectralInst`, `d = 3`, `L = 3`, `W = 2`, `N = 216`, `H = 1`; `inst_spectral` `:587`, `inst_block` `:607`, `inst_identity` `:617`, `inst_mass` `:637`, `inst_bad` `:644`)
```lean
-- JakSpectral.lean:573-586: namespace JakSpectralInst; abbrev H1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ := 1; def y0 := 0; def a0 := 0; private I_im_ne, I_im_pos
theorem inst_block :
    ∀ hH : H1.IsHermitian,
    blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) y0 =
        (((2 * 3) ^ 3 : ℕ) : ℂ) *
          ∑ x, ((‖hH.eigenvectorBasis y0 x‖ ^ 2 : ℝ) : ℂ) * scirc 3 3 2 (1 / 2) x y0 ∧
      blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) y0 =
        ((unMy 3 3 2 (1 / 2) (fun x => hH.eigenvectorBasis y0 x) y0 : ℝ) : ℂ) :=
  fun hH => ⟨blockM_eq (by norm_num) _ hH y0 y0, blockM_eq_unMy (by norm_num) _ hH y0 y0⟩

-- (`inst_spectral` :587-606 and `inst_identity` :617-636 omitted here, same shape: `fun hH => ⟨targets 1a-1e⟩`, resp. `⟨target 3a, target 3b⟩` at `z = I`, `σ₁ = true`, `σ₂ = false`)
theorem inst_mass :
    ∀ hH : H1.IsHermitian,
    ∑ α, ‖blockM 3 3 2 (1 / 2) hH a0 α‖ ≤ 2 * (((2 * 3) ^ 3 : ℕ) : ℝ) :=
  fun hH => sum_norm_blockM_le (by norm_num) _ hH a0

/-- `inst_bad` (target 5b at `Ω = Unit`, `P = δ_()`, `Hr ≡ 1`, `lam = 1`, `𝔡 = 1/10`, `E = 1`, `p = 1`;
every hypothesis discharged: `3 ≤ 3`, `1 ≤ 2`, `0 < 1/10`, `2^{-3/2 + 1/10} ≤ 1`, `δ(·) ≤ 1`). -/
theorem inst_bad :
    ∀ hH : ∀ _ω : Unit, H1.IsHermitian,
    (MeasureTheory.Measure.dirac ()) {ω : Unit | ∃ α, |(hH ω).eigenvalues α - 1| ≤
        (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
      ((2 : ℕ) : ℝ) ^ (-((1 / 10 : ℝ) / 6)) ≤ ‖blockM 3 3 2 1 (hH ω) (siteBlock 3 3 2 y0) α‖} ≤
      ((2 * 3 + 1 : ℕ) : ℝ≥0∞) * 1 := by
  intro hH
  refine measure_bad_le_of_queBadMat (MeasureTheory.Measure.dirac ()) (by norm_num)
    (lam := 1) (𝔡 := 1 / 10) (E := 1) (by norm_num) (by norm_num) ?_ y0 hH 1 (fun b => prob_le_one)
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

end JakSpectralInst
```

### Name-clash grep (`grep -rnw <name> RBM3D RBM3D.lean --include='*.lean'`, excluding the new file and `RBM3D/Probe`; hits per public name)
```
spectralPole: 0 spectralGsigPole: 0 siteBlock: 0 blockM: 0 Gres_sq_apply_self: 0 Gres_apply_self_spectral: 0 Gres_sq_apply_self_spectral: 0 spectralGsigPole_norm_eq_spectralPole: 0 isOrthoEigenbasis_eigenvectorBasis: 0 blockM_eq: 0 blockM_eq_unMy: 0 green_spectral_identity_blockM: 0 norm_green_spectral_identity_blockM_le: 0 sum_norm_blockM_le: 0 unBadY_of_blockM: 0 measure_bad_le_of_queBadMat: 1 JakSpectralInst: 0
only hit: RBM3D/Universality/Pins.lean:403 (docstring citing the RBM2D name)
```

### Port source
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf
c9a24cf
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/JakSpectral.lean
 RBM2D/Universality/JakSpectral.lean | 216 ++++++------------------------------
 1 file changed, 35 insertions(+), 181 deletions(-)
```
Ported from RBM2D/Universality/JakSpectral.lean at c9a24cf (read with `git show c9a24cf:...`): `:51-171` -> section 1 (`JakSpectral.lean:40-211`); `:175-256` -> section 2 (`:213-277`); `:260-416` -> section 3 (`:278-435`); `:420-522` -> section 4 (`:436-540`); `:526-589` -> section 5 (`:541-570`). Template for the private `JakSpectral_Gres_eq_spectral`: `RBM3D/Main/FixedZ.lean:552-600` (`hinv` step).

### Narrative
- Private `Gres` decomposition: route (iii), second option: the `hinv` step of `FixedZ.lean:552-600`, generic in an `IsOrthoEigenbasis`, giving `Gres H w true = U diag((μ-w)⁻¹) U*`; `σ = false` is `Gres H z̄ true` by `simp [Gres]`.
- `blockM` has the `SBR d L lam b a0` weights (target 2); `blockM_eq_unMy` is `unMy_eq` plus `star ψ * ψ = ↑‖ψ‖²`; `blockM_eq` unfolds `unMy`, `scirc`.
- Mass bound: private column sum `JakSpectral_sum_svarF_col` (`Finset.sum_fiberwise`, `card_Iblk`, `SBR_comm`, `sum_SBR_row`), `svarF_nonneg`, `card_Idx`, completeness `JakSpectral_sum_sq_norm`.
- `unBadY_of_blockM` takes the eigenpair from Mathlib; `measure_bad_le_of_queBadMat` is `measure_mono` plus the merged `unBadY_measure_le`, same hypotheses.
- No hypothesis added; no `3 ≤ d`; no signature of a merged file changed; `Test/Axioms.lean` untouched (`git diff --stat main...t/T2251`: only `RBM3D/Universality/JakSpectral.lean`, 675 insertions).
- Not targets (as in the ticket): no pin is proved (`UNJak`, `UNUyw`, `UNJakUywRow`, `UNJakk`, `UNUywk`, `UNJakUywRowk`, `UNJakUywRowBA` stay owed); `Gsig`, `Epaper`, `Spaper`, `sbSupport` are not added.
- Special-case note: `blockM`, the identities and the union bound are the general `d`, `lam`, `L ≥ 3`, `W ≥ 1` statements; only the instances are at `d = 3`.
- RBM2D `measure_bad_le_of_queBadMat` is restated at the `UNBadY` data (window `N⁻¹ W^{𝔡/3}`, threshold `W^{-𝔡/6}`, `queBadMat` at `(𝔡/3, 𝔡/6)`, factor `2d + 1`), as the ticket pins.
- Root import: left to the hub (`RBM3D.lean` untouched), so the full `lake build` in the worktree does not compile the new module; its own build and the registry pre-check above do.

## (c) Verified Mathlib names
Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvectorBasis, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.IsHermitian.mulVec_eigenvectorBasis, orthonormal_iff_ite, EuclideanSpace.inner_eq_star_dotProduct, Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_eq_right_inv, Unitary.coe_mul_star_self, Complex.normSq_eq_conj_mul_self, Complex.conj_mul', Complex.norm_natCast, Complex.norm_real, MeasureTheory.measure_biUnion_finset_le, Finset.sum_fiberwise, Real.rpow_le_one_of_one_le_of_nonpos, MeasureTheory.prob_le_one, Matrix.isHermitian_one (all used in the compiled file; none searched absent).

## (d) Open issues and paper-delta candidates
- Open issues: none. All targets 1-6 compiled; no hypothesis added.
- T2251a (design table, no paper statement): portmap row UN-19 counts `unMy_eq`, `unBadY_subset`, `unBadY_measure_le` and "+300 for the `d ≥ 3` weights", merged in UN-01 (`Pins.lean:1125-1355`); the file is 675 lines (ticket estimate 730); RBM2D `green_eq_spectral`/`green_apply_self` have no public twin in `Pins`' closure (private `JakSpectral_Gres_eq_spectral`); RBM2D `measure_bad_le_of_queBadMat` restated at the `UNBadY` data.
- No new paper-delta T2251b: no statement of the ticket needed a change.
