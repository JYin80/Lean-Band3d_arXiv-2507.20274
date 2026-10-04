Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 23:17:06 UTC 2026

Sources: RBM2D `Path/StepDecompLoop` (783 lines) and `Path/Kernel` (355 lines) read at `c9a24cf` (`git show`). Merged `main` at `07ede19`.
Token counts below are `grep -c` line counts on those two files (tool log, this session).

### (i) Exponent table (each `W²`/`Z2`/`d = 2` occurrence, and every constant of the targets)

| item (occurrences: Kernel / StepDecompLoop) | d = 2 form | d ≥ 3 replacement | constraint | value at d=3, L=3, W=2 / slack |
|---|---|---|---|---|
| `Z2 L` (27 / 36) | `Z2 L` | `Zd d L` (R2); only finite sums, `Θ`-commutation | none | 27 blocks |
| `Theta L`, `SB L` (10 / 0) | fixed profile | `Theta d L g ξ`, `SB d L g`, `g = sz.lam n`; `hS : ‖SB d L g‖ = 1` is `norm_SB d L g hL` (`3 ≤ L`, any real `g`); `ukerMat` gains `(d, g)` | `3 ≤ L` (already in every Kernel statement) | `SB` row sums = 1, 6 = 2d neighbours per row (script) |
| `Idx L W`, `BlockIndex L W` (0 / 21, 11) | `Z2 (W*L)`, `Z2 L × Fin (W^2)` | `Idx d L W`, `Vtx d L W` | card `= (L W)^d` | 216 = (WL)^3 fine points, 27 blocks of 8 |
| `(L*W)^2`, `Sizes.size` (0 / 4, 11) | `N=(WL)^2` | `(L*W)^d = sz.size n` (`card_BlockIndex`) | `N = (WL)^d` | N = 216 |
| `W⁻¹ ^ 2` = `e`, bound of `‖E_p‖` (0 / 7) | `W^{-2}` | `e = (W^d)⁻¹` (`E_p = W^{-d}·1_{[p]}`) | `e ≤ 1` (`W ≥ 1`) | e = 1/8, e² = W^{-2d} = 1/64 |
| first jet `|φ₁| ≤ N·2K³e²‖D‖`, `K = η⁻¹` | `N 2 η⁻³ W⁻⁴` | `N·2η⁻³·W^{-2d}‖y‖` (2 words, product rule; d-free apart from N, e) | `|φ₁| ≤` it | bound 54; measured max 3.27e-2 |
| second jet `|φ₂| ≤ N·6K⁴e²‖D‖²` (3 words, each twice) | `N 6 η⁻⁴ W⁻⁴` | `N·6η⁻⁴·W^{-2d}‖y‖²` | `|φ₂| ≤` it | bound 324; measured max 2.67e-1 |
| (H3) constant `C₂ = 6 N η⁻⁴` (statement of `hermTestFun_loopPM`) | same | same (`W^{-2d} ≤ 1` for `W ≥ 1`, `W_pos`) | `C₂ ≥ N 6 η⁻⁴ W^{-2d}` | C₂ = 20736 = 324 · W^{2d} (slack factor 64); η = (1-u)Im m = 1/2 |
| `ξ = |m|²` | `normSqSpectralMOne` | `=1` for `|E| ≤ 2` from `‖mE E‖ = 1` (`norm_mE`), d-free | `|E| ≤ 2` | `m(0) = i`, `|m|² = 1` |
| weights `U b a = (K_{b1 a1} K_{b2 a2}).re`, `K = (1 - vξS)Θ_{wξ}` | `ukerNonneg` | same: `K = 1 + (w-v)ξ SΘ_{wξ}` with `S ≥ 0` entrywise (`sbKernelR ≥ 0`, any `g`) and `Θ = Σ (wξ)^k S^k`; d-free | `ξ ≥ 0`, `0 ≤ v ≤ w`, `wξ < 1` | min entry 1.5e-3 > 0; `Σ_a U = ((1-v)/(1-w))²` = 2.25 at (1/4,1/2) |
| time window (DECISIONS §29) | `0≤u<1`, `|E|<2`, `0≤v≤w<1`, `0 ≤ Δ` | unchanged | `η > 0` iff `u < 1`; `w < 1` keeps `Θ_w` bounded | boundaries run in (ii-b): u=0 η=1; u=.999 η=1e-3; w=.999 row sum 500; v=0, v=w ok; Δ=0 gives `Y=0`, `ξ=0` |
| step bound `(Σ_a|U|)(C₂/2)Δ‖X‖²` and `L²` bound `4((Σ_a|U|)C₂/2)²Δ²∫‖X‖⁴` | same | same, `X` from `seqXmat` (variance `W^{-d}S^{(B)}(g)`) | statement of `stepDecomp` (T2073) | Σ_a U = 2.25, C₂/2 = 10368; the `768N⁸` moment constants do not occur (the integral stays in the statement) |
| Duhamel telescope (`Uop_duhamel_telescope`) | `Z2 L × Z2 L → ℂ` | `Zd d L × Zd d L → ℂ`; algebraic: semigroup `K(v,w)K(u,v) = K(u,w)` from `mul_Theta`, `Theta_commute(_SB)` (merged, `hS` from `norm_SB`) | `‖ξ‖ ≤ 1`, `0 ≤ u_j < 1` | residuals 2e-15 (semigroup), 7e-16 (m=2) |

Dependency finding (not in the ticket or its check file). `stepDecomp_loopPM` as ported uses `ukerNonneg` and `normSqSpectralMOne`
(`StepDecompLoop.lean`, `StepDecompLoop_weight_nonneg`, 6 grep hits), which RBM2D defines in `Path/UBounds` (lines 416-440 plus helpers 105-215, 238, 262-295).
The portmap row for `Path/UBounds` is ST2-25, whose dependencies list ST2-24 (`Path/Kernel`); ST2-24 imports `Path/UBounds` in RBM2D (portmap level 2 `StepDecompLoop <- ... Path/UBounds`).
No `ukerNonneg` or `normSqSpectralMOne` exists in merged `RBM3D` (grep over `RBM3D/` returned nothing). Route: copy the needed proof as `private` helpers with the file stem
(ST1-COMMON item 4), `normSqSpectralMOne` from `norm_mE`, `ukerNonneg` via the Neumann series (`Theta_eq_tsum` is merged). Public statements are unchanged.
Other statement-level changes for the prover: `gloop (blockMat M) z (pmLoop p q)` becomes the merged `loopPM d L W E u M p q` (`RBM.Green`) or `loopL`; RBM3D lacks `gloop_two_plus_minus_nonneg`
and `loopFine_pm_formula` is private, so `loopPM_real_of_herm` is re-proved from `tr(G E_p G* E_q) = W^{-2d} Σ_{y∈[q],x∈[p]} |G_{yx}|²` (script: `Im tr` ≤ 5e-18).

### (ii) One concrete nondegenerate instance (a: stepDecomp_loopPM and Duhamel at d=3, L=3, W=2; b: boundaries)

Data: d=3, L=3, W=2 (N=216, 27 blocks), g=sz.lam=1/2, E=0, u=1/2 (η=1/2), v=1/4, w=1/2, ξ=|m|²=1, grid s=1/4, Δ=(t-s)/K=1e-3 with K=2, j=0, label b arbitrary (all 729 checked), one sample ω=(X₀,X₁,X₂),
`H_k = √s X₀ + √Δ Σ_{i≤k} X_i`. Hypotheses of `stepDecomp_loopPM`: 0≤u=1/2<1, |E|=0<2, 0≤v=1/4≤w=1/2<1, 0≤Δ=1e-3: all hold. No external hypothesis occurs (every hypothesis is deterministic), so no limit computation applies.
Lean instance to use: `Sizes 3` with `L n = n+3`, `W n = n+2`, `lam n = 1/2` (n=0 gives L=3, W=2).
Scripts: scratchpad `T2085/check.py`, `T2085/bnd.py` (numpy; `Φ_a = tr(G E_p G* E_q)`, `G = (H-z)⁻¹`, `z = E+(1-u)m`; `Z_b = √Δ Σ_a U(b,a) D_{X₁}Φ_a(H₀)` by the analytic jet, validated by finite differences;
`E[·|F₀]` by 1500 antithetic Monte Carlo draws of X₁; `Y_b := ξ_b - Z_b`, so line (i) of the theorem is definitional and lines (iii)-(v) are the checks).

```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2085 && python3 check.py
SB row sums min/max 0.9999999999999999 1.0000000000000002  neighbours per row 6 (2d = 6 )
W^d E|X_ij|^2 vs W^d S_ij (300 samples; averaged over entries of equal S): [(0.1, 0.1), (0.4, 0.4016)]
m(E)= 1j  |m|^2= 1.0  z= 0.5j  eta= 0.5
ukerMat min entry 1.518e-03 (>=0), row sum 1.500000 vs (1-v xi)/(1-w xi)=1.500000
ukerMat_mul resid ||K(v,w)K(u,v)-K(u,w)||=2.22e-15 ; ukerMat_self resid=1.11e-15
tr(G E_p G* E_q) label (0, 0) : direct (0.220041357417-0j)  formula 0.220041357417
tr(G E_p G* E_q) label (3, 17) : direct (0.000191128608-0j)  formula 0.000191128608
max |Im tr(G E_p G* E_q)| over a few labels: 5.2583805365546965e-18
jets vs central differences: d1 max|.|=3.272e-02 resid 2.98e-08 ; d2 max|.|=2.672e-01 resid 1.89e-07
(H3): max_a |phi2_a| = 2.672e-01 <= N*6*eta^-4*W^-2d = 3.240e+02 <= C2=6N eta^-4 = 2.074e+04
(H1')  max_a |phi1_a| = 3.272e-02 <= N*2*eta^-3*W^-2d = 5.400e+01
sum_a U(b,a) = ((1-v)/(1-w))^2 ?  2.250000 vs 2.250000 (xi=1)
(i)   xi_b, Z_b computed independently, Y_b := xi_b - Z_b (definitional): max|xi|=2.221e-03 max|Z|=2.145e-03 max|Y|=1.331e-04
(iii) max_b |Y_b| / rhs_b = 7.314e-07 (rhs_b min 1.820e+02); ||X1||=1.970 E||X||^2~3.921 E||X||^4~15.399
(iv)  MC mean of Z_b over 400 draws: max|.|=8.73e-05 vs std/sqrt(400)=5.23e-05 
(v)   one-sample |Y_b|^2 max = 1.772e-08 <= 4 (sumU C2/2)^2 Delta^2 E||X||^4 = 3.352e+04 (min over b) -> ratio max 5.286e-13
Duhamel (m=2, u_j=[0.25, 0.251, 0.252]): max|A_2|=2.4475e-01, max|lhs-rhs|=7.49e-16
Duhamel (m=1): max|lhs-rhs|=0.00e+00
first-step increment size max|A_1-A_0|=1.89e-03, max|A_1-U_{01}A_0|=2.11e-03 (Delta=0.001)

$ python3 bnd.py
v=0 w=0: min entry 0.00e+00, row sum 1 vs 1
v=0 w=0.5: min entry 3.04e-03, row sum 2 vs 2
v=0.25 w=0.25: min entry -3.40e-17, row sum 1 vs 1
v=0.25 w=0.5: min entry 1.52e-03, row sum 1.5 vs 1.5
v=0.5 w=0.999: min entry 1.84e+01, row sum 500 vs 500
v=0.999 w=0.999: min entry -1.28e-14, row sum 1 vs 1
Duhamel boundary grid u=[0.0, 0.25, 0.9, 0.999]: rel resid 3.01e-11
E=0 u=0: eta=1.000e+00 |m|^2=1.000000000000
E=1.99 u=0.5: eta=4.994e-02 |m|^2=1.000000000000
E=0 u=0.999: eta=1.000e-03 |m|^2=1.000000000000
```

Reading of the output: line (iii) is the pathwise bound with `C₂ = 6Nη⁻⁴` and E[‖X‖²] by Monte Carlo (slack factor about 1e6); (v) is the `L²` bound (one-sample proxy for the integral); (iv) shows `E[Z_b|F₀] ≈ 0` within Monte Carlo error
(the maximum over 729 labels of the sample mean is 1.7 standard errors); the conditional mean of `ξ_b` is zero by construction of the estimate. The kernel entries `-3e-17`, `-1e-14` at `v = w` are rounding of exact zeros (`K = 1`).

### Verdicts
- `Path/Kernel` (`ukerMat`, `Uop`, `uopSemigroup`, `Uop_duhamel_telescope`, `_stopped`): PASS. Every statement holds at d ≥ 3 with `hS := norm_SB d L g hL`; semigroup and telescope residuals ≤ 3e-11 at d=3, boundary times included.
- `Path/StepDecompLoop` (`hermTestFun_loopPM`, `loopPM_real_of_herm`, `stepDecomp_loopPM`, `stepDecomp_Z_subG_loopPM`): PASS. The exponents close (`C₂ = 6Nη⁻⁴` with slack `W^{2d}`), all hypotheses hold at the instance. Condition: the dependency finding above (private copy of `normSqSpectralMOne`, `ukerNonneg` from `UBounds`) must be handled in the ticket; without it `stepDecomp_loopPM` does not compile.

## (b) Script output — Sat Oct  3 23:46:29 UTC 2026

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2085 && lake build RBM3D.Path.Kernel RBM3D.Path.StepDecompLoop   # tail
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3360 jobs).
exit=0
(lines containing 'error' in the full output: 0)
$ git diff --stat main...t/T2085
 RBM3D/Path/Kernel.lean         | 374 ++++++++++++++++
 RBM3D/Path/StepDecompLoop.lean | 960 +++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1334 insertions(+)
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Path/Kernel.lean RBM3D/Path/StepDecompLoop.lean
RBM3D/Path/Kernel.lean:0
RBM3D/Path/StepDecompLoop.lean:0
$ lake env lean pre.lean   # CONTROL §20 registry pre-check: import RBM3D + both new modules + #assert_rbm_axioms (after lake build RBM3D)
exit=0 (stdout head: axiom audit: 2814 theorems, 1110 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).)
$ #print axioms of every public declaration of both files (21 names, one script)
ukerMat : [propext, Classical.choice, Quot.sound]
Uop : [propext, Classical.choice, Quot.sound]
UopSemigroup : [propext, Classical.choice, Quot.sound]
ukerMat_mul : [propext, Classical.choice, Quot.sound]
ukerMat_self : [propext, Classical.choice, Quot.sound]
Uop_add : [propext, Classical.choice, Quot.sound]
Uop_smul : [propext, Classical.choice, Quot.sound]
Uop_self : [propext, Classical.choice, Quot.sound]
Uop_comp : [propext, Classical.choice, Quot.sound]
UopHom : [propext, Classical.choice, Quot.sound]
uopSemigroup : [propext, Classical.choice, Quot.sound]
duhamel_telescope : [propext, Classical.choice, Quot.sound]
duhamel_telescope_stopped : [propext, Classical.choice, Quot.sound]
Uop_grid_semigroup : [propext, Classical.choice, Quot.sound]
Uop_factor : [propext, Classical.choice, Quot.sound]
Uop_duhamel_telescope : [propext, Classical.choice, Quot.sound]
Uop_duhamel_telescope_stopped : [propext, Classical.choice, Quot.sound]
hermTestFun_loopPM : [propext, Classical.choice, Quot.sound]
loopPM_real_of_herm : [propext, Classical.choice, Quot.sound]
stepDecomp_loopPM : [propext, Classical.choice, Quot.sound]
stepDecomp_Z_subG_loopPM : [propext, Classical.choice, Quot.sound]
```

### Target statements (extracted by sed from the files)
```
$ sed -n 44,53p RBM3D/Path/Kernel.lean ; sed -n 101,104p ; sed -n 289,297p
/-- The one-index kernel `(1 - v ξ S^{(B)}) Θ^{(B)}_{w ξ}` of `𝒰_{v,w}` (`def_Ustz`;
`Kernel:45`). -/
def ukerMat (ξ : ℂ) (v w : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  (1 - ((v : ℂ) * ξ) • SB d L g) * Theta d L g ((w : ℂ) * ξ)

/-- `𝒰_{v,w,(+,-)}` on two-index tensors (`def_Ustz`); for `σ = (+,-)` both slots
carry `m_i m_{i+1} = |m|²` (`Kernel:50`). -/
def Uop (ξ : ℂ) (v w : ℝ) (A : Zd d L × Zd d L → ℂ) : Zd d L × Zd d L → ℂ :=
  fun a => ∑ b : Zd d L × Zd d L, ukerMat d L g ξ v w a.1 b.1 * ukerMat d L g ξ v w a.2 b.2 * A b

/-- At equal times the one-index kernel is the identity (`Kernel:93`; port of RBM1D `edgeKer_self`,
`Hierarchy/Kernel.lean:120`). -/
theorem ukerMat_self (hL : 3 ≤ L) {ξ : ℂ} {v : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1) :
    ukerMat d L g ξ v v = 1 :=
/-- **The algebraic part of (105)** (`int_K-L_ST`) in `Uop` form (`Kernel:263`):
`A_m = 𝒰_{u_0,u_m} A_0 + Σ_{j<m} 𝒰_{u_{j+1},u_m} (A_{j+1} - 𝒰_{u_j,u_{j+1}} A_j)`,
for grid times with `0 ≤ u_j < 1` at the indices `j ≤ m`. -/
theorem Uop_duhamel_telescope (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1)
    (u : ℕ → ℝ) (m : ℕ) (hu0 : ∀ j ≤ m, 0 ≤ u j) (hu1 : ∀ j ≤ m, u j < 1)
    (A : ℕ → (Zd d L × Zd d L → ℂ)) :
    A m = Uop d L g ξ (u 0) (u m) (A 0) +
      ∑ j ∈ Finset.range m, Uop d L g ξ (u (j + 1)) (u m)
        (A (j + 1) - Uop d L g ξ (u j) (u (j + 1)) (A j)) := by
$ sed -n 603,617p RBM3D/Path/StepDecompLoop.lean   # hermTestFun_loopPM
theorem hermTestFun_loopPM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hE : |E| < 2) (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    HermTestFun sz n
        (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)
      ∧ ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
          M.IsHermitian → y.IsHermitian →
          ‖fderiv ℝ (fderiv ℝ
              (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
                loopPM d (sz.L n) (sz.W n) E u M a.1 a.2)) M y y‖
            ≤ 6 * (sz.size n : ℝ) * (etaT E u)⁻¹ ^ 4 * ‖y‖ ^ 2 := by
  have _ := hu0
  have hη : 0 < etaT E u := etaT_pos hE hu1
$ sed -n 664,667p ; sed -n 692,694p RBM3D/Path/StepDecompLoop.lean   # loopPM_real_of_herm ; stepDecomp_loopPM (head)
theorem loopPM_real_of_herm {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (a : Zd d (sz.L n) × Zd d (sz.L n))
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    (loopPM d (sz.L n) (sz.W n) E u M a.1 a.2).im = 0 := by
theorem stepDecomp_loopPM {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (E u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : |E| < 2) (v w : ℝ) (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1)
    (hΔ : 0 ≤ gridStep s t K n) (b : Zd d (sz.L n) × Zd d (sz.L n)) :
$ grep -n '∧ (∀ᵐ\|∧ ((pathP\|∧ ∫\|≤ 4 \*\|∧ Measurable\|    (∀ ω, stepXi' RBM3D/Path/StepDecompLoop.lean   # heads of the five conjuncts of stepDecomp_loopPM (full statement: lines 692-755)
695:    (∀ ω, stepXi sz s t K n j
715:      ∧ Measurable[filt sz j] (fun ω => Ab sz s t K n j
721:      ∧ (∀ᵐ ω ∂(pathP sz), ‖stepY sz s t K n j
737:      ∧ ((pathP sz)[stepY sz s t K n j
744:      ∧ ∫ ω, ‖stepY sz s t K n j
751:          ≤ 4 * ((∑ a : Zd d (sz.L n) × Zd d (sz.L n),
```

### Compiled nonempty instances (all in the files, d = 3, L = 3, W = 2 where W occurs)
```
$ grep -n "^example\|^private theorem StepDecompLoop_check" RBM3D/Path/Kernel.lean RBM3D/Path/StepDecompLoop.lean
RBM3D/Path/Kernel.lean:325:example : UopSemigroup 3 3 (1 / 2) := uopSemigroup 3 3 (1 / 2)
RBM3D/Path/Kernel.lean:329:example (A : Zd 3 3 × Zd 3 3 → ℂ) :
RBM3D/Path/Kernel.lean:337:example (A : ℕ → (Zd 3 3 × Zd 3 3 → ℂ)) (m : ℕ) :
RBM3D/Path/Kernel.lean:349:example {Ω' : Type*} (τ : Ω' → ℕ) (ω : Ω') (k : ℕ) (A : ℕ → (Zd 3 3 × Zd 3 3 → ℂ)) :
RBM3D/Path/Kernel.lean:365:example : ukerMat 3 3 (1 / 2) 1 (1 / 4) (1 / 4) = 1 :=
RBM3D/Path/Kernel.lean:368:example : ukerMat 3 3 (1 / 2) 1 (1 / 2) (3 / 4) * ukerMat 3 3 (1 / 2) 1 (1 / 4) (1 / 2)
RBM3D/Path/StepDecompLoop.lean:920:example := hermTestFun_loopPM StepDecompLoop_sizes 0 0 (1 / 2) (by norm_num) (by norm_num)
RBM3D/Path/StepDecompLoop.lean:924:example : (loopPM 3 (StepDecompLoop_sizes.L 0) (StepDecompLoop_sizes.W 0) 0 (1 / 2)
RBM3D/Path/StepDecompLoop.lean:931:example (b : Zd 3 (StepDecompLoop_sizes.L 0) × Zd 3 (StepDecompLoop_sizes.L 0)) :=
RBM3D/Path/StepDecompLoop.lean:940:private theorem StepDecompLoop_check_Z_subG
$ sed -n 919,936p RBM3D/Path/StepDecompLoop.lean
`u = 1/2`, label `(0, 0)`: the observable is in the class and satisfies (H3). -/
example := hermTestFun_loopPM StepDecompLoop_sizes 0 0 (1 / 2) (by norm_num) (by norm_num)
  (by norm_num [abs_of_nonneg]) (0, 0)

/-- **`loopPM_real_of_herm` at the concrete instance** (`M = 1` is Hermitian, `216 × 216`). -/
example : (loopPM 3 (StepDecompLoop_sizes.L 0) (StepDecompLoop_sizes.W 0) 0 (1 / 2)
    (1 : Matrix (Idx 3 (StepDecompLoop_sizes.L 0) (StepDecompLoop_sizes.W 0))
      (Idx 3 (StepDecompLoop_sizes.L 0) (StepDecompLoop_sizes.W 0)) ℂ) 0 0).im = 0 :=
  loopPM_real_of_herm StepDecompLoop_sizes 0 0 (1 / 2) (0, 0) Matrix.isHermitian_one

/-- **`stepDecomp_loopPM` at the concrete instance** `E = 0`, `u = 1/2`, `v = 1/4`, `w = 1/2`,
`j = 0`, on the private size sequence with `d = 3`, `L = 3`, `W = 2`. -/
example (b : Zd 3 (StepDecompLoop_sizes.L 0) × Zd 3 (StepDecompLoop_sizes.L 0)) :=
  stepDecomp_loopPM StepDecompLoop_sizes (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
    0 (1 / 2) (by norm_num) (by norm_num) (by norm_num [abs_of_nonneg]) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [gridStep]) b

/-- **`stepDecomp_Z_subG_loopPM` at the concrete instance** `E = 0`, `u = 1/2`, `j = 0`, on the
```

### Name-clash grep (new public names against RBM3D main, `git grep -nwE "(theorem|lemma|def|abbrev|structure|axiom) <name>" main -- RBM3D/*.lean`)
```
ukerMat:0 Uop:0 UopSemigroup:0 ukerMat_mul:0 ukerMat_self:0 Uop_add:0 Uop_smul:0 Uop_self:0 Uop_comp:0 UopHom:0 uopSemigroup:0 duhamel_telescope:0 duhamel_telescope_stopped:0 Uop_grid_semigroup:0 Uop_factor:0 Uop_duhamel_telescope:0 Uop_duhamel_telescope_stopped:0 hermTestFun_loopPM:0 loopPM_real_of_herm:0 stepDecomp_loopPM:0 stepDecomp_Z_subG_loopPM:0 
```

### Port source (RBM2D, read-only)
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h   # HEAD
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/Kernel.lean RBM2D/Path/StepDecompLoop.lean
 RBM2D/Path/Kernel.lean         | 151 ++++++-----------------------------
 RBM2D/Path/StepDecompLoop.lean | 177 +++--------------------------------------
 2 files changed, 35 insertions(+), 293 deletions(-)
$ public names of RBM2D Path/Kernel + Path/StepDecompLoop at c9a24cf (git show | grep) vs RBM3D: identical sets (21 names), none dropped
```

### Narrative (the files and the logs above are the evidence)
- Two new files, one commit on `t/T2085` (`1a3d1b3`): `RBM3D/Path/Kernel.lean` (374 lines), `RBM3D/Path/StepDecompLoop.lean` (960 lines). `git diff --stat main...t/T2085` above shows no other file. `RBM3D/Test/Axioms.lean` is unchanged: the pre-check (§20) exits 0 and neither file declares a `Prop` that a lemma takes as a hypothesis (`UopSemigroup` is proved by `uopSemigroup` and is not a hypothesis anywhere).
- Port: all 21 public names of RBM2D `Path/Kernel` (17) and `Path/StepDecompLoop` (4) at `c9a24cf` are kept, none dropped (name lists compared by script in this stage).
- Statement changes (class b): `ukerMat`/`Uop` and every kernel statement gain `(d, L, g)` for the propagator `Theta d L g`, `SB d L g` (ST1-COMMON items 2, 4). `3 ≤ L` is the only constraint, `g` is free (the merged `*_of_three_le` forms discharge `‖SB‖ = 1`). The (H3) constant is `C₂ = 6 N η⁻⁴`, `N = sz.size n = (LW)^d`; the proof gives the sharper `6 N η⁻⁴ (W^{-d})^2` and the step `W^{-d} ≤ 1` is `hW` in `hermTestFun_loopPM`. The `d = 2` exponent `W^{-4}` becomes `W^{-2d}` inside the proof; the stated constant is unchanged.
- Weights sign: RBM3D has no `ukerNonneg` or `normSqSpectralMOne` (finding in (a)); `StepDecompLoop_ukerNonneg` (private, `StepDecompLoop.lean:530`) proves `ukerMat ≥ 0` entrywise for `ξ ≥ 0`, `0 ≤ v ≤ w < 1` from `Theta_real_eq`, `Theta_real_nonneg` (`Props4`) and `ukerMat = 1 + (w - v) ξ S Θ`; `|m|² = 1` is `norm_mE`. No public statement changed because of it.
- `loopPM_real_of_herm` is re-proved by cyclicity of the trace (RBM3D lacks `gloop_two_plus_minus_nonneg`), as its docstring says.
- Duhamel telescope: `Uop_duhamel_telescope` and the stopped form keep RBM2D's hypotheses (`0 ≤ u_j < 1` for `j ≤ m`, `‖ξ‖ ≤ 1`); the `d = 3`, `L = 3`, `g = 1/2` instances above discharge every one (`u j = j/(j+2)`).
- Instances: `stepDecomp_loopPM` at `d = 3`, `L = 3`, `W = 2`, `E = 0`, `u = 1/2`, `v = 1/4`, `w = 1/2`, `s = 1/4`, `t = 3/4`, `K = 2`: every hypothesis is deterministic and discharged by `norm_num`; the size sequence is the private `StepDecompLoop_sizes` (`L n = n+3`, `W n = n+2`, `lam n = 1/2`), not the merged `sz0`. `stepDecomp_Z_subG_loopPM` is applied on the whole space through the private variance-proxy lemma `StepDecompLoop_exists_variance_bound` (`StepDecompLoop_check_Z_subG`).
- Not done in this stage: the numerical scripts of (a) were not re-run; the residuals in (a) are the preflight's.

## (c) Verified Mathlib / project names
- Used and compiled in the two modules (each occurs in `StepDecompLoop.lean`, grep count 1; build exit 0 above): `Finset.abs_sum_le_sum_abs`, `Matrix.trace_mul_comm`, `Matrix.trace_conjTranspose`, `Complex.conj_eq_iff_im`, `pow_le_one₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `Nat.one_le_cast`, `Complex.abs_re_le_norm`.
- Project names used (grep hit in `RBM3D/`): `norm_matrix_trace_le_card_mul` (`Gauss/FlowCalculus.lean:600`), `Theta_real_eq` (`Propagator/Props4.lean:173`), `Theta_real_nonneg` (`:177`), `norm_mE` (`Defs/Semicircle.lean:63`), `mul_Theta_of_three_le` (used in `ukerMat_self`).
- Verified absent in `RBM3D/` (grep, preflight): `ukerNonneg`, `normSqSpectralMOne`, `gloop_two_plus_minus_nonneg`.

## (d) Open issues and paper-delta candidates
- T2085a: `ukerMat`, `Uop`, `UopSemigroup`, `uopSemigroup` and the `Uop_*` lemmas carry the explicit propagator parameters `(d, L, g)` (RBM2D: `L` only); for the model `g = sz.lam n`. No change of the mathematics (`def_Ustz`).
- T2085b: `hermTestFun_loopPM`, `stepDecomp_loopPM`: the proof uses `W^{-2d}` where RBM2D has `W^{-4}`; the stated `C₂ = 6 N η⁻⁴` has `N = (LW)^d`.
- T2085c: `StepDecompLoop_ukerNonneg` (private) duplicates what RBM2D has in `Path/UBounds` (ST2-25); once ST2-25 is ported the copy can be replaced; no public name depends on it.
- Observation: the docstring of `stepDecomp_loopPM` cites "candidate `T2080a`/`T2080b`" (text inherited from RBM2D `StepDecompLoop.lean:530` at `c9a24cf`; those tags are `docs/paper-deltas.md` D143/D144 of another ticket); no statement is affected.

## Repair (audit round 1, `docs/reports/T2085-audit.md` §7 items 1–2) — Sat Oct  3 23:53:08 UTC 2026

```
$ git log --oneline -1 && git diff --stat 1a3d1b3 HEAD
042dae0 T2085: repair docstring tags of stepDecomp_loopPM (audit round 1)
 RBM3D/Path/StepDecompLoop.lean | 2 +-
 1 file changed, 1 insertion(+), 1 deletion(-)
$ grep -n "T2080\|T2085f" RBM3D/Path/StepDecompLoop.lean
691:`T2085f`); the fifth conjunct is `stepDecomp_Y_sq` (candidate `T2085f`). -/
$ lake build RBM3D.Path.StepDecompLoop   # tail
✔ [3360/3360] Built RBM3D.Path.StepDecompLoop (4.0s)
Build completed successfully (3360 jobs).
exit=0   (lines containing 'error', case-insensitive: 0)
$ lake env lean ax.lean   # O2: the name missing from the axiom list in (b)
'RBM.Path.UopHom_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.stepDecomp_loopPM' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Comment-only change; no statement, proof or instance changed. The public names are in namespace `RBM.Path` (22 names: the 21 in (b) plus `UopHom_apply`).

Additional paper-delta candidates (audit D1–D3):
- T2085d (D1): `ukerMat` (`Kernel.lean:46`), `Uop` (`:51`), `UopSemigroup` (`:56`), `uopSemigroup` (`:173`) and the `Uop_*` lemmas
  (`:108–:311`) formalize the evolution kernel `𝒰^{(n)}_{s,t,σ}` of `(def_Ustz)` (Definition `DefTHUST`, `3_5_Loop_Hierarchy.tex:108–118`)
  only for `n = 2`, with one scalar `ξ` in both index slots, i.e. `σ = (+,-)` with `M^{(+,-)} = |m|²` at the use site
  (`StepDecompLoop.lean:692`, `:788`); the paper defines it for every `n ≥ 2`, `σ ∈ {+,-}^n`, with `M^{(σ_i,σ_{i+1})}` per slot.
- T2085e (D2): `Uop_duhamel_telescope` (`Kernel.lean:292`), `Uop_duhamel_telescope_stopped` (`:311`) and the abstract `duhamel_telescope`
  (`:193`), `duhamel_telescope_stopped` (`:236`) are a discrete grid telescope
  `A_m = 𝒰_{u_0,u_m}A_0 + Σ_{j<m} 𝒰_{u_{j+1},u_m}(A_{j+1} − 𝒰_{u_j,u_{j+1}}A_j)` for any sequence `A`; the paper's `(int_K-L_ST)`,
  `(int_K-LcalE)` (Lemma `Sol_CalL`, `3_5_Loop_Hierarchy.tex:134–147`) are the continuous-time Duhamel formulas with the
  `[𝒦 ∼ (𝓛−𝒦)]`, `𝓔^{(𝓛−𝒦)×(𝓛−𝒦)}`, `𝓔^{G̃}` and martingale `d𝓔^M` integrals. Lean has only the algebraic (semigroup) part.
- T2085f (D3): `stepDecomp_loopPM` (`StepDecompLoop.lean:692`) and `stepDecomp_Z_subG_loopPM` (`:788`) are Lean-only statements of the
  time discretization (one grid step `ξ_b = Z_b + Y_b`, measurability of `Ab`, pathwise bound, vanishing conditional mean of `Y_b`,
  the fifth (`L²`, `stepDecomp_Y_sq`) conjunct; conditional sub-Gaussianity of `1_S Z_b`); the paper has no such statement. The weights
  `Σ_a U b a` replace `Σ_a |U b a|`, which needs `0 ≤ v ≤ w < 1` (`hv`, `hvw`, `hw`). The docstring of `stepDecomp_loopPM` now cites
  `T2085f` in place of RBM2D's tags `T2080a`/`T2080b` (in RBM3D those are D143/D144 of another ticket).
