Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 07:26:04 UTC 2026

### (i) Exponent table
All targets are deterministic inequalities for one Hermitian matrix on `Idx d L W` (`N = (W L)^d`); no exponent of `N`, `W`, `L`, `d` occurs.
The only constants are the explicit ones below, and `d` enters only through `N`, `scirc d L W lam`, `blockM d L W lam`, `card_Idx`.

| quantity | value / form | constraint it must satisfy | slack at the instance (d=3,L=3,W=2,lam=1/2,N=216) |
|---|---|---|---|
| `N` | `(W L)^d` (`card_Idx`, `Defs/Sizes.lean:107`) | `N>0` (`NeZero L`, `NeZero W`) | `N=216` |
| `hL` | `3 ≤ L` | needed by `blockM_eq`, `sum_norm_blockM_le`, `norm_green_spectral_identity_blockM_le` (via `sum_SBR_row`, `unMy_eq`); no `3 ≤ d`, no L-W relation | `L=3`, slack 0 (allowed) |
| column sum `∑_x svarF x y` | `1` for every `lam` (`JakSpectral_sum_svarF_col` `JakSpectral.lean:445`) | `svarF ≥ 0`, `SBR` row sum `1` | script: column sums all 1, `S`=`Sᵀ`, `S ≥ 0` |
| `∑_x (S_xy + N⁻¹)` | `2` (`JakSpectral_profile_weight_sum` `:496`) | `‖scirc x y‖ ≤ S_xy + N⁻¹` (`:474`) | script: `2.0` |
| mass bound `∑_α‖M_{a0,α}‖` | `≤ 2N` (`sum_norm_blockM_le` `:509`) | any `lam` | `432`; script `max_y ∑_α|M| = 320 ≤ 432` (non-scalar diagonal data) |
| deloc from grid | grid event gives `|ψ_α(x)|² ≤ 2ηt·Cb` (window mass `≤ 2(r+2η)Cb` at `r=0`); with `M_{y,α} = N ∑_x |ψ_α(x)|² S°_xy` and `∑_x(S_xy+N⁻¹)=2` this gives `‖M‖ ≤ 2N·2ηt Cb = 4Nηt Cb` | `jakGridGood H ηt Cb u.re (2^k ηt)` | `4·216·1·1 = 864` (not used by the instance: `Bad ≡ False` uses `θ=432`) |
| window mass (1c) | `≤ 2(r+2η)Cb`; covering (1b): `≤ 2η ∑_{j<⌈r/η⌉₊+1} Im G` | `0<η`, `0≤r`, `0≤Cb`; Lorentzian `η/((λ-c_j)²+η²) ≥ 1/(2η)` when `|λ-c_j| ≤ η`; `⌈r/η⌉₊+1 ≤ r/η+2` | numerics (vi): `lhs-rhs ≤ -0.558` (1b), `≤ -1.52` (1c) |
| `θ` | `≥ 0`; `hBad`: `‖M_{a0,α}‖ ≤ θ` for `¬Bad a0`, `|λ_α-u.re| ≤ w'` | | `θ = 432 = 2N` (every entry `≤ ∑_α`, from `sum_norm_blockM_le`); script `max|M| = 9.8 ≤ 432` |
| `α₁` | `≥ θ(ηt/u.im²)(N Cb) + 4Nηt Cb(2N Cb(4/w'+4ηt/w'²)) + ((2^{K'}w')²)⁻¹ 2N` | | `93312 + 2985984 + 108 = 3079404`, slack 0 (equality) |
| `α₂` | `≥ 4Nηt Cb (ηt/u.im² · N Cb)` | | `4·216·216 = 186624`, slack 0 |
| `Qb` | `≥ 6(ηt/u.im)Cb + 8K Cb + (2^K ηt)⁻¹` | | `6+8+1/2 = 29/2`, slack 0 |
| scales | `0<u.im ≤ ηt`, `0<(w j).im ≤ ηt`, `0≤Cb`, `0<w'`, `0≤θ` | | `u.im = (w 0).im = ηt = Cb = w' = 1`, `K=K'=1`; slack 0 |
| grid hypotheses | `hG1..hG4`: `Im G_xx ≤ Cb` on the grids | at `η=1`: `Im G_xx ≤ η⁻¹ = 1` for every Hermitian `H` (`gridGood_one`; math: `η/((λ-E)²+η²) ≤ η⁻¹`, `∑_l|ψ_l(x)|²=1`) | slack 0 at `Cb=1`; script (B): grid `Im G ≤ 1` verified |
| crude (2b) | RHS `∏(Im w_j)⁻¹ · 2(Im u)⁻³` | `Im m ≤ (Im w)⁻¹`, `∑_α|pole|²‖M‖ ≤ (Im u)⁻²·2N`, `∑_γ|pole||ψ_γ(y)|² ≤ (Im u)⁻¹` | `2·1`; random `H`: `0.0136 ≤ 16` at `Im u = 1/2` |
| 1a (new public) | `Im Gres H (E+iη) true x x = ∑_l η|ψ_l(x)|²/((λ_l-E)²+η²)`, `0<η` (RBM2D had `η ≠ 0`) | route: `Gres_apply_self_spectral hH (hη: 0<z.im) true x` (`JakSpectral.lean:155`), `spectralPole = (λ - z)⁻¹` (`:48`), `Im (λ-E-iη)⁻¹ = η/((λ-E)²+η²)` | all uses (1b, 1c, instances, UN-22) have `η>0`; script: `1.69110560709814 = 1.69110560709813` |
| `stieltjesN` | `(card ι)⁻¹ · tr (Gres M z true)` (`Pins.lean:88`); `Im m = N⁻¹∑_l η/((λ_l-E)²+η²)` | route: sum 1a over `x`, `Finset.sum_comm`, `∑_x|ψ_l(x)|²=1` (the private `JakSpectral_unit_norm`-type copy, `:236`); `η ↦ η Im m` nondecreasing | `Im m(i) = 1/2` at `H=1` |

Token check (consumer shape). `UNJak` integrand (`Pins.lean:700-704`) is `(∏ j∈s, (stieltjesN M (z j)).im) * ‖∑ x, (Gres M (z i) b₁ * Gres M (z i) b₁) x x * scirc d (sz.L n) (sz.W n) (sz.lam n) x y * Gres M (z i) b₂ y y‖`; the left sides of 2a/2b (check file §2.3) are this at `H=M`, `u=z i`, `w=z`, `lam=sz.lam n`; `UNJakk` (`PinsK.lean:365-376`) is the same with `lam = K.lamV sz n`. The check file's `example` at §3 compiled (CONTROL `done:` line, 07:23:46 UTC, exit 0).

Dependence on the source. RBM2D `green` is `Gres · · true`, `Gsig H u σ ^ 2` is `Gres H u σ * Gres H u σ` (`JakSpectral.lean:173` already uses this form); column sums use `svarF` instead of `Spaper` with the same constant `2`. The RBM2D file at `c9a24cf` has 1121 lines; the sister working tree is at `9e0f275` (945 lines), so the port must be read via `git show c9a24cf:RBM2D/Universality/JakKernel.lean`.

### (ii) One concrete nondegenerate instance
Data: `d=3`, `L=3`, `W=2` (`N=216`), `lam=1/2`, `u = w 0 = I`, `ηt=Cb=w'=1`, `K=K'=1`, `Bad ≡ False`, `θ=432`, `α₁=3079404`, `α₂=186624`, `Qb=29/2`.
(A) `H=1` (check data): every hypothesis holds; but the LHS of 2a/2b is `≈ 1e-17` (`G` is scalar and `∑_x S°_xy = 0`), so the inequality is nearly vacuous there, although no hypothesis is.
(B) non-scalar `H = diag(x₀.val)` (eigenbasis = standard basis), `u = 1/2 + i`, `w 0 = -1 + i`, same constants: the LHS is `0.0368 > 0`. Optional for stage 1b (ticket: not pinned).
(C) random Hermitian `H` (`N=216`) for 1a, 1b, 1c, 2b.
Command (script is Python/numpy, no Lean; `SBR`, `sbKernelR`, `zdistD` as in `Propagator/Props4.lean:48`, `Defs/Block.lean:74`, `Defs/Lattice.lean:71`):
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2267/pf.py`
Output (verbatim, last 22 lines):
```
N 216 col sums S True sym True sum_x(S+1/N) [2. 2.] S>=0 True
theta 432 alpha1 3079404.0 alpha2 186624.0 Qb 14.5
A H=1 True True LHS 9.813077866773595e-18 RHS2a 206719.25 RHS2b 2.0 Im m 0.5
A H=1 True False LHS 9.813077866773595e-18 RHS2a 206719.25 RHS2b 2.0 Im m 0.5
A H=1 False True LHS 9.813077866773595e-18 RHS2a 206719.25 RHS2b 2.0 Im m 0.5
A H=1 False False LHS 9.813077866773595e-18 RHS2a 206719.25 RHS2b 2.0 Im m 0.5
B grid Im G<=Cb=1: True
B max|M| 9.8 <=432: True colsum 319.9999999999999 <=432: True
B True True 2a LHS 0.03677137582948555 RHS 206719.25 | y=5 LHS 0.03677137582948555 | 2b LHS 0.03677137582948555 RHS 2.0
B True False 2a LHS 0.03677137582948555 RHS 206719.25 | y=5 LHS 0.03677137582948555 | 2b LHS 0.03677137582948555 RHS 2.0
B False True 2a LHS 0.03677137582948555 RHS 206719.25 | y=5 LHS 0.03677137582948555 | 2b LHS 0.03677137582948555 RHS 2.0
B False False 2a LHS 0.03677137582948555 RHS 206719.25 | y=5 LHS 0.03677137582948555 | 2b LHS 0.03677137582948555 RHS 2.0
1a 1.691105607098137 1.6911056070981314
1b/1c max over x of (lhs-rhs): -0.558431552154039 -1.5220618925967255 Cb 2.3605997544850283 K 7
2b True True 0.0136415007557236 <= 16.0
2b True False 0.013641500755723639 <= 16.0
2b False True 0.013641500755723818 <= 16.0
2b False False 0.013641500755723816 <= 16.0
```
(`RHS2a = N⁻¹ · α₁ · Qb = 3079404·14.5/216 = 206719.25`; the line "B ... 2b" repeats the 2a LHS since `s={w0}` there; the 2b rows at the end use `s=∅`, `u=0.3+0.5i`, `Im u = 0.5`, `y=0`, `lam=1/2`, RHS `2(Im u)⁻³ = 16`; 1b/1c rows: `η=0.05`, `r=0.3`, `E₀=0.1`, `K=⌈r/η⌉₊+1=7`, every `x ∈ [0,216)`.)
External hypothesis: none (no external or pin hypothesis; no limit computation needed). The numbers (`3 ≤ 3`, `0<1`, `1 ≤ 1`, `0 ≤ 1`, `0<1`, three constants at equality) are all discharged by `norm_num`; no `N = 0`, empty index, collapsed window, or `False` premise (`Bad ≡ False` is a predicate, its `hBad` hypothesis is discharged by `sum_norm_blockM_le`).

### Verdicts
- 1a `im_Gres_apply_self`: PASS (true for `0<η`; route `Gres_apply_self_spectral` merged).
- 1b `sum_mass_window_le_im_green`, 1c `sum_mass_window_le_of_im_green_le`: PASS.
- 2a `jak_pointwise_good`, 2b `jak_pointwise_crude`: PASS (constants close at `N=216` with equality, no slack needed; every dimension-dependent input is merged).
- 3 instances (`im_Gres_le_inv`, `gridGood_one`, `blockM_le_432`, `inst_window`, `inst_good`, `inst_crude`): PASS (all hypotheses hold at the data above).
- Overall: PASS.

## (b) Script output

Branch `t/T2267`, commit `9e9a4bf` (one file: `RBM3D/Universality/JakKernel.lean`, 1092 lines). `git diff --stat main...t/T2267`: 1 file changed, 1092 insertions. `RBM3D/Test/Axioms.lean`: untouched (`git diff 8bb6f82 HEAD -- RBM3D/Test/Axioms.lean | wc -l` = 0; 8bb6f82 is the branch base).

Build (`lake build RBM3D.Universality.JakKernel`, run at Tue Oct  6 07:36:55 UTC 2026 after `touch`; exit 0; lines of the module and the last line; no warning for the module):
```
ℹ [3330/3330] Replayed RBM3D.Universality.JakKernel
info: RBM3D/Universality/JakKernel.lean:1080:0: 'RBM.Univ.im_Gres_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/JakKernel.lean:1081:0: 'RBM.Univ.sum_mass_window_le_im_green' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/JakKernel.lean:1082:0: 'RBM.Univ.sum_mass_window_le_of_im_green_le' depends on axioms: [propext, Classical.choice, Quot.sound
info: RBM3D/Universality/JakKernel.lean:1083:0: 'RBM.Univ.jak_pointwise_good' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/JakKernel.lean:1084:0: 'RBM.Univ.jak_pointwise_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/JakKernel.lean:1085:0: 'RBM.Univ.JakKernelInst.im_Gres_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/JakKernel.lean:1086:0: 'RBM.Univ.JakKernelInst.gridGood_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/JakKernel.lean:1087:0: 'RBM.Univ.JakKernelInst.blockM_le_432' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/JakKernel.lean:1088:0: 'RBM.Univ.JakKernelInst.inst_window' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/JakKernel.lean:1089:0: 'RBM.Univ.JakKernelInst.inst_good' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/JakKernel.lean:1090:0: 'RBM.Univ.JakKernelInst.inst_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3330 jobs).
```

Target statements extracted by script (`/…/T2267/mkreport.py`, first lines of each declaration up to `:=`):
```lean
theorem im_Gres_apply_self {H : Matrix n n ℂ} (hH : H.IsHermitian) (E : ℝ) {η : ℝ}
    (hη : 0 < η) (x : n) :
    (Gres H (E + η * Complex.I) true x x).im =
      ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x) / ((hH.eigenvalues l - E) ^ 2 + η ^ 2) := by

theorem sum_mass_window_le_im_green {H : Matrix n n ℂ} (hH : H.IsHermitian) {η r : ℝ}
    (hη : 0 < η) (_hr : 0 ≤ r) (E₀ : ℝ) (x : n) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤
      2 * η * ∑ j ∈ Finset.range (⌈r / η⌉₊ + 1),
        (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im := by

theorem sum_mass_window_le_of_im_green_le {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {η r Cb : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (hCb : 0 ≤ Cb) (E₀ : ℝ) (x : n)
    (hG : ∀ j ∈ Finset.range (⌈r / η⌉₊ + 1),
      (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im ≤ Cb) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤ 2 * (r + 2 * η) * Cb := by

def jakGridGood (H : Matrix n n ℂ) (η Cb E₀ r : ℝ) : Prop :=

theorem jak_pointwise_good (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) {ηt Cb w' θ α₁ α₂ Qb : ℝ} (hηu : 0 < u.im) (hηu' : u.im ≤ ηt)
    (hηw : ∀ j, 0 < (w j).im) (hηw' : ∀ j, (w j).im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hθ : 0 ≤ θ) (K K' : ℕ)
    (hG1 : ∀ k ≤ K, jakGridGood H ηt Cb u.re (2 ^ k * ηt))
    (hG2 : ∀ k ≤ K', jakGridGood H ηt Cb u.re (2 ^ k * w'))
    (hG3 : jakGridGood H ηt Cb u.re 0)
    (hG4 : ∀ j, jakGridGood H ηt Cb (w j).re 0)
    (Bad : Zd d L → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
      ‖blockM d L W lam hH a0 α‖ ≤ θ)
    (hα₁ : θ * (ηt / u.im ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * Cb)) +
        4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb *
          (2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (((W * L) ^ d : ℕ) : ℝ)) ≤ α₁)
    (hα₂ : 4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb *
        (ηt / u.im ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * Cb)) ≤ α₂)
    (hQb : 6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ ≤ Qb)
    (y : Idx d L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ ≤
      (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ((((W * L) ^ d : ℕ) : ℝ)⁻¹ *
          ((α₁ + (if Bad (siteBlock d L W y) then α₂ else 0)) * Qb)) := by

theorem jak_pointwise_crude (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) (hηu : 0 < u.im) (hηw : ∀ j, 0 < (w j).im)
    (y : Idx d L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ ≤
      (∏ j ∈ s, (w j).im⁻¹) * (2 * (u.im⁻¹) ^ 3) := by

```

Compiled nonempty instances (namespace `RBM.Univ.JakKernelInst`, `d = 3`, `L = 3`, `W = 2`, `N = 216`, `H = 1` and, for 2a, also non-scalar `H2`):
```lean
theorem im_Gres_le_inv {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η) (E : ℝ) (x : n) :
    (Gres H ((E : ℂ) + η * Complex.I) true x x).im ≤ η⁻¹ := by

theorem gridGood_one {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (E₀ r : ℝ) : jakGridGood H 1 1 E₀ r := by

theorem blockM_le_432 {H : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hH : H.IsHermitian) (lam : ℝ)
    (a0 : Zd 3 3) (α : Idx 3 3 2) : ‖blockM 3 3 2 lam hH a0 α‖ ≤ 432 := by

theorem inst_window :
    ∀ hH : H1.IsHermitian,
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - 0| ≤ 1),
        ‖hH.eigenvectorBasis l y0‖ ^ 2 ≤ 2 * (1 + 2 * 1) * 1 :=

theorem inst_good (y : Idx 3 3 2) (σ₁ σ₂ : Bool) :
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN H1 Complex.I).im) *
        ‖∑ x, (Gres H1 Complex.I σ₁ * Gres H1 Complex.I σ₁) x x *
          scirc 3 3 2 (1 / 2) x y * Gres H1 Complex.I σ₂ y y‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), (1 / Complex.I.im * 1)) *
        ((((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((3079404 + (if False then (186624 : ℝ) else 0)) * (29 / 2))) :=

theorem inst_crude (σ₁ σ₂ : Bool) :
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN H1 Complex.I).im) *
        ‖∑ x, (Gres H1 Complex.I σ₁ * Gres H1 Complex.I σ₁) x x *
          scirc 3 3 2 (1 / 2) x y0 * Gres H1 Complex.I σ₂ y0 y0‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), Complex.I.im⁻¹) * (2 * (Complex.I.im⁻¹) ^ 3) :=

example (y : Idx 3 3 2) (σ₁ σ₂ : Bool) :=
  jak_pointwise_good (d := 3) (L := 3) (W := 2) (by norm_num) (1 / 2) H2_herm
    ({0} : Finset (Fin 1)) (fun _ => (⟨-1, 1⟩ : ℂ)) (⟨1 / 2, 1⟩ : ℂ) (ηt := 1) (Cb := 1) (w' := 1)
    (θ := 432) (α₁ := 3079404) (α₂ := 186624) (Qb := 29 / 2) (by simp) (by simp)
    (fun _ => by simp) (fun _ => by simp) zero_le_one one_pos (by norm_num) 1 1
    (fun _ _ => gridGood_one H2_herm _ _) (fun _ _ => gridGood_one H2_herm _ _)
    (gridGood_one H2_herm _ _) (fun _ => gridGood_one H2_herm _ _) (fun a : Zd 3 3 => a = 0)
    (fun a0 _ α _ => blockM_le_432 H2_herm _ a0 α) (by norm_num) (by norm_num) (by norm_num)
    y σ₁ σ₂
```

Statement check against the ticket check file (sections 2.2-2.4 of `docs/tickets/checks/T2267-check.lean` pasted into a scratch file that imports the new module, plus `example : T2267_<name> := @<name>` for all 11 statements and `T2267_H1 = JakKernelInst.H1`, `T2267_y0 = JakKernelInst.y0` by `rfl`; `jakGridGood` in it is the library one):
```
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2267/scratch_check.lean ; echo "exit $?"
exit 0   (no output)
```

`#print axioms` (lines of the build above): `im_Gres_apply_self`, `sum_mass_window_le_im_green`, `sum_mass_window_le_of_im_green_le`, `jak_pointwise_good`, `jak_pointwise_crude`, `JakKernelInst.im_Gres_le_inv`, `gridGood_one`, `blockM_le_432`, `inst_window`, `inst_good`, `inst_crude`: all `[propext, Classical.choice, Quot.sound]`.

Hygiene and name-clash greps:
```
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/JakKernel.lean | wc -l
       0
$ for n in jakGridGood im_Gres_apply_self sum_mass_window_le_im_green sum_mass_window_le_of_im_green_le jak_pointwise_good jak_pointwise_crude JakKernelInst im_Gres_le_inv gridGood_one blockM_le_432 inst_window inst_good inst_crude H2_herm; do echo "$n: $(grep -rnw $n RBM3D RBM3D.lean | grep -v Universality/JakKernel.lean | wc -l | tr -d " ")"; done
jakGridGood: 0
im_Gres_apply_self: 0
sum_mass_window_le_im_green: 0
sum_mass_window_le_of_im_green_le: 0
jak_pointwise_good: 0
jak_pointwise_crude: 0
JakKernelInst: 0
im_Gres_le_inv: 0
gridGood_one: 0
blockM_le_432: 0
inst_window: 0
inst_good: 0
inst_crude: 0
H2_herm: 0
$ grep -nw "RBM.green\|Gsig\|Spaper\|Epaper" RBM3D/Universality/JakKernel.lean
16:`scirc d L W lam`, `N = (W L)^d`, the merged resolvent `Gres` (RBM2D `RBM.green`, `Gsig`) and the
$ grep -n "^import" RBM3D/Universality/JakKernel.lean
6:import RBM3D.Universality.JakSpectral
7:import Mathlib.Algebra.Order.Floor.Semiring
8:import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
```

Registry pre-check (`import RBM3D` + `import RBM3D.Universality.JakKernel` + `#assert_rbm_axioms`, temporary file outside the worktree; `lake env lean`, exit 0). Its output equals the output of the same file without the `JakKernel` import except line 1 (`diff`):
```
1c1
< axiom audit: 7774 theorems, 2578 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).   [without JakKernel]
> axiom audit: 7788 theorems, 2582 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).   [with JakKernel]
premises found by scanning: 155 (borrowed 1, owed 97, structural 40, refuted 6, superseded 11).
registry: 2 borrowed + 157 owed + 102 structural + 7 refuted + 12 superseded; 125 registered premise(s) carry nothing yet
```
No new premise, no registry line added or deleted, no refuted/superseded name used (no pin occurs in any statement).

Port source: RBM2D `Universality/JakKernel.lean` at `c9a24cf` (read with `git show c9a24cf:...`; 1121 lines), `Delocalization.lean:89` (`im_green_apply_self`, formula only).
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf
c9a24cf
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/JakKernel.lean
 RBM2D/Universality/JakKernel.lean | 254 ++++++--------------------------------
 1 file changed, 39 insertions(+), 215 deletions(-)
```

Narrative (facts from the file and the tool log):
- The only hit of `RBM.green`/`Gsig`/`Spaper`/`Epaper` (whole words) in the file is the module docstring (line 16); the code uses `Gres`, `svarF`, `scirc` only. `Green/EntryCore`, `Universality/InjSum`, `Main/*` are not imported (the import list above).
- Port map: RBM2D `:49-150` (covering, 1b, 1c), `:155` (`jakGridGood`), `:161-611` (private grid/`stieltjesN`/dyadic/pole lemmas), `:615-836` (block), `:848`, `:927` (2a, 2b), `:961-1114` (instances) became the file's sections 1-7 with: `RBM.green H w` to `Gres H w true`, `Gsig H u σ ^ 2` to `Gres H u σ * Gres H u σ`, `Scirc L W` to `scirc d L W lam`, `blockM L W hH` to `blockM d L W lam hH`, `siteBlock L W` to `siteBlock d L W`, `Idx L W` to `Idx d L W`, `Z2 L` to `Zd d L`, `(W L)^2` to `(W L)^d`, `lam` after `hL`.
- New relative to the source: target 1a `im_Gres_apply_self` (from `Gres_apply_self_spectral` at `σ = true`, `0 < η`; the ticket's route (ii)); the private `JakKernel_stieltjesN_im_eq_diag` (`Im m = N⁻¹ ∑_x Im G_xx`, from `stieltjesN` = `(card)⁻¹ * trace`) and `JakKernel_stieltjesN_im_eq` (sum of 1a over `x`, `Finset.sum_comm`, `∑_x |ψ_l(x)|² = 1` via the ported `JakKernel_sum_sq_norm_col`); the `svarF` column-sum copies `JakKernel_sum_svarF_col`, `JakKernel_scirc_norm_le`, `JakKernel_profile_weight_sum` (copies of the private `JakSpectral_*` lemmas `:445, :474, :496`); `card_Idx` (merged) replaces `JakKernel_card_idx`.
- Constants are those of the preflight table: `α₁ = 3079404`, `α₂ = 186624`, `Qb = 29/2`, `θ = 432`; all three constant hypotheses and `hBad` are discharged in `inst_good` by `norm_num` and `blockM_le_432` (no hypothesis kept open, no pin used).
- Instances: `H = 1` for 1c, 2a, 2b, plus one `example` for 2a at the non-scalar `H2 = diag(x₀.val)` with `u = 1/2 + i`, `w 0 = -1 + i`, `Bad a₀ ↔ a₀ = 0` (the preflight's data (B); the ticket marks it optional).
- No pin is proved or stated; `UNJak`, `UNUyw`, `UNJakUywRow`, `UNJakk`, `UNUywk`, `UNJakUywRowk`, `UNJakUywRowBA` stay owed. `jakRow`, the probability layer, the pair kernel, `RBM.green`, `Gsig`, `Spaper` are not used in the file.
- Not a general statement beyond its hypotheses: 2a is conditional on the grid events `hG1`-`hG4`, the window bound `hBad` and the constants; 2b holds for every Hermitian matrix. Both are per-sample deterministic inequalities.
- Main moved after the branch point: the branch is based on 8bb6f82; `main` is at 061aa73 (`git show --stat 061aa73`: T2266 merge, touches `Test/Axioms.lean` (2 deletions), `Universality/EMCTE2.lean`, not this ticket's file). The hub should expect no conflict (this branch changes only `JakKernel.lean`).

## (c) Verified Mathlib names (all compile in the file)
- `Nat.le_ceil`, `Nat.ceil_lt_add_one`, `Nat.floor_le`, `Nat.lt_floor_add_one`: `Mathlib.Algebra.Order.Floor.Semiring`.
- `Finset.prod_le_prod₀`: `Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset`.
- `Finset.sum_fiberwise`, `Finset.single_le_sum`, `Finset.sum_comm`, `Finset.sum_div`, `Finset.mul_sum`, `Finset.sum_filter`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.prod_nonneg`.
- `Complex.inv_im`, `Complex.im_sum`, `Complex.re_sum`, `Complex.mul_im`, `Complex.normSq_eq_norm_sq`, `Complex.normSq_apply`, `Complex.abs_im_le_norm`, `Complex.abs_re_le_norm`, `Complex.norm_natCast`.
- `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `div_le_div_iff₀`, `div_le_iff₀`, `le_div_iff₀`, `inv_mul_le_iff₀`, `sum_geometric_two_le`.
- `Matrix.isHermitian_one`, `Matrix.isHermitian_diagonal_iff`, `Matrix.trace`, `Matrix.diag`, `EuclideanSpace.norm_eq`, `Real.sqrt_eq_one`, `Unitary.coe_mul_star_self`.
- Verified by `grep -rn "def Spaper\|def Epaper" RBM3D` (0 hits): `Spaper`, `Epaper` are absent in RBM3D and not added. `RBM.green` (`Green/EntryCore.lean:34`) and `Gauss.Gsig` (`Loop/GLoop.lean:92`, takes `ω E t`) exist but are outside the import closure of this file and unused; the merged `Gres` is used.

## (d) Open issues and paper-delta candidates
- T2267a (design table, no paper statement; ticket's own candidate): portmap row UN-20 (`T2162-portmap.md:214`) role `prover-hard` to `prover`; actual size 1092 lines (estimate 970 to 1120). UN-22 (`UywKernel`) should use `im_Gres_apply_self` for its one `RBM.im_green_apply_self`.
- No statement of the ticket was changed; no T2267b: every statement of check sections 2.2-2.4 elaborates as written and is identical up to the check's `Type` vs `Type*` (scratch check exit 0).
- Hub notes: root import `import RBM3D.Universality.JakKernel` is added at merge after the last `import` line of `RBM3D.lean`; `Test/Axioms.lean` untouched.
