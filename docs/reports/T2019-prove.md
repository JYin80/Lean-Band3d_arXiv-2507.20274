Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 03:33:03 UTC 2026

Notation: `e = 1-t`, `s₀ = (1+2dg²)⁻¹`, `γ = t s₀ g² = lgGam d g t`, `Δ_j = 2 - T_j - T_j⁻¹`, `f_τ(x) = min(x²/τ, x)`,
`x_j = zdist L (a_j)`, `Σ_j x_j = zdistD d L a`. Merged inputs read in `/Users/junyin/Lean_proof/RBM3D-wt/T2019` (main `022103c`).

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `1 - tS` | `= e·1 + γ Σ_j Δ_j` (matrix identity) | `S = s₀·1 + γ/t·Σ_j(T_j+T_j⁻¹)`; constant part `1 - t s₀`; `e + 2dγ = 1 - t + 2d t s₀ g²`; equal because `s₀(1+2dg²) = 1`, i.e. `t s₀ + 2d t s₀ g² = t` | exact; needs the `2d` neighbours distinct (`3 ≤ L`); asserted entrywise to `< 10⁻¹²` in (ii) (all 54 parameter points) |
| 2 | symbol on `χ_k` | `e + 2γ Σ_j(1 - cos(2πk_j/L)) ≥ e` | `> 0` for `t < 1` | `≥ 1-t`; `=` at `k = 0` |
| 3 | `‖SB‖ = 1` (hypothesis of `eq_Theta_of_mul`) | `RBM.norm_SB d L g (hL : 3 ≤ L)` (`Defs/Block.lean:136`) | merged, no new hypothesis | closes the `hS` argument |
| 4 | `‖(t:ℂ)‖ < 1` | `t < 1`, `0 ≤ t` | pin hypotheses | exact |
| 5 | Laplace integrand | `0 ≤ e^{-es}K_{γs}(a) ≤ e^{-es}` (`hkT_mass`: `hkT ≥ 0`, `Σ_x hkT = 1`, so each `hkT ≤ 1`) | integrable on `(0,∞)` since `e > 0` | `∫ = 1/e` bound |
| 6 | `t = 0` | `γ = 0`, `hkT L 0 x = δ_{x,0}`, integral `= δ_{a,0}` | `Θ_0 = 1` | exact |
| 7 | `d = 0` (pin has `∀ d`) | `Zd 0 L` one point, `SB = 1`, `K = 1`, `γ = t g²`: `Θ = 1/(1-t) = ∫e^{-es}ds` | consistent | exact |
| 8 | SumMin, case all `x_j ≤ τ` | `Σ x_j²/τ ≥ X²/(dτ)` (Cauchy–Schwarz) | `≥ (1/d)·min(X²/τ, X)` | factor `1` |
| 9 | SumMin, case some `x_j > τ` | `A = {x_j ≥ τ}`, `S_A ≥ τ`, `B` = rest (`|rest| ≤ d-1`); RHS `≥ S_A + B²/((d-1)τ)`; LHS `≤ (S_A+B)/d` | `S_A(1-1/d) + B²/((d-1)τ) ≥ 2B√(S_A/(dτ)) ≥ 2B/√d ≥ B/d` (AM–GM, `S_A ≥ τ`) | `2/√d` vs `1/d`: ratio `2√d ≥ 2`; `d = 1` has `B = 0` (separate trivial case) |
| 10 | SumMin without `1/d` | false: `x = (1,50,0), τ = 10`: `51 > 50.1` | `1/d` needed | `(ii)`: 80349/200000 random violations, 0 with `1/d` |
| 11 | 1D constants (`hkT_le`, read at `HeatTorus1D.lean:226,248,275`; `hkZ_*` witnesses in `HeatBounds1D.lean:637,673,737`) | `C₀ = 128, c₀ = 1/16`; `C₁ = 3181, c₁ = 1/32`; `C₂ = 1.324·10⁵, c₂ = 1/32` (witness `C_Z·coth(c_Z/16)`) | statements are `∃ C c`; the table fixes the formulas, Lean may `obtain` | the prover may use the `obtain`ed values; formulas below are in them |
| 12 | `c* = min(c₀,c₁,c₂)` | `1/32` | `> 0` | — |
| 13 | exponent loss | `c = c*/d` (`d = 3`: `1/96 = 0.010417`) | SumMin: `Σ_j f(x_j) ≥ (1/d) f(Σ x_j)` | loss `1/d`, unavoidable (row 10) |
| 14 | KProdBound | `C = C₀^d` (`d = 3`: `2.097·10⁶`), `min(1,τ^{-1/2})^d = min(1,τ^{-d/2})` | `τ ≤ L²`, `τ > 0` | exact power; `(ii)` max ratio `4.9·10⁻⁷` |
| 15 | KProdDiff1 | one factor `= Δ_j hkT` at `a_j` (no argument shift): `C = C₁C₀^{d-1}` (`5.21·10⁷`), exponent `min(1,τ^{-1})·min(1,τ^{-1/2})^{d-1} = min(1,τ^{-(d+1)/2})` | | max ratio `1.9·10⁻⁸` |
| 16 | KProdDiff2, `i ≠ j` | two factors differenced at `a_i`, `a_j` (no shift): `C = C₁²C₀^{d-2}` (`1.30·10⁹`), power `τ^{-1}τ^{-1}τ^{-(d-2)/2}` for `τ ≥ 1`, i.e. `min(1,τ^{-(d+2)/2})` | | max ratio `7.8·10⁻¹⁰` |
| 17 | KProdDiff2, `i = j` | `hkT(x+2) + hkT(x) - 2hkT(x+1)` = `hkT_diff2` at `x+1`; exponent at `zdist(x+1)` vs `zdist x`: `|f_τ(n') - f_τ(n)| ≤ |n'-n| ≤ 1` (`f_τ' = min(2n/τ,1) ≤ 1`); `C = C₂C₀^{d-1}e^{c*}` (`2.24·10⁹`; the ticket's "2" also works, `e^{2c*}`) | `τ^{-3/2}·τ^{-(d-1)/2} = τ^{-(d+2)/2}` | max ratio `9.0·10⁻¹⁰` |
| 18 | gap, 1D input | `hkT_gap`: `(C,c) = (1, 4)` (`HeatTorus1D.lean:614`); `0 ≤ x_j ≤ (1+C)/L` from `|x_j - 1/L| ≤ (C/L)e^{-cτ/L²} ≤ C/L` | `τ ≥ L²` | `x_j ≤ 2/L` |
| 19 | gap telescoping | `|∏x_j - L^{-d}| ≤ Σ_j L^{-(j-1)}·(C/L)e^{-cτ/L²}·((1+C)/L)^{d-j}`, so constant `d·C(1+C)^{d-1}` (ticket's `d(1+C)^{d-1}` with the 1D `C` of the bound included) `= 12` at `d = 3` | `L^{-(j-1)} ≤ ((1+C)/L)^{j-1}` | factor `≥ 1` |
| 20 | gap diff1 / diff2 | `C(1+C)^{d-1}` (`4`), mixed `C²(1+C)^{d-2}e^{-2cτ/L²}` (`2`, `e^{-2c·} ≤ e^{-c·}`), same `C(1+C)^{d-1}` (`4`, at `x+1`); common `C_d = 12`, `c = 4` | powers `L^{-(d+1)}`, `L^{-(d+2)}` | max ratios `7.7·10⁻¹¹`, `4.6·10⁻¹⁰`; zero-mode `4.8·10⁻⁷` |
| 21 | regime split | `τ ≤ L²` uses `hkT_le/diff1/diff2`; `τ ≥ L²` uses `hkT_gap` | both closed at `τ = L²` | pins have `τ ≤ L²` and `L² ≤ τ`, no gap between |

Verdict on closing: all exponents close; constants depend on `d` (and on the 1D constants) only, never on `L`, `g`, `t`, `τ`, `a`.

### (ii) Concrete nondegenerate instance and checks

Command (numpy only; pure Python, no Lean): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/pf2019.py`

```
LaplaceProd and identity 1-tS=e+gam*sum Delta_j: max |integral - inverse entry| = 9.769962616701378e-15
1D constants: C0=128 c0=0.0625 | C1=3181 c1=0.03125 | C2=1.324e+05 c2=0.03125 | c*=0.03125
d=3 product constants: KProdBound C=2.097e+06; Diff1 C=5.212e+07; Diff2 mixed 1.295e+09, same 2.238e+09 (incl e^c*); c=c*/d=0.010417
gap: hkT_gap (C,c)=(1,4); d*C*(1+C)^(d-1)=12, C(1+C)^(d-1)=4, C^2(1+C)^(d-2)=2 -> C_d=12, c=4
d=3, L in {3,5,8}: max LHS/RHS with preflight constants (must be <= 1):
  B    4.881e-07  OK
  D1   1.925e-08  OK
  D2m  7.822e-10  OK
  D2s  8.969e-10  OK
  G0   4.787e-07  OK
  G1   7.697e-11  OK
  G2   4.618e-10  OK
SumMin: violations of 1/d version 0, of version without 1/d 80349 (of 200000)
instance x=(1,50,0), tau=10: LHS=(1/3)*min(260.1,51)=17.0000, RHS=50.1000, no-1/d LHS=51
instance Theta: gamma=0.071429 (=t g^2/(1+2dg^2)=1/14), e=0.50, eps=e/gamma=7.00
Theta_{1/2}(0,0) inverse entry = 1.123076923077 ; Laplace-product integral = 1.123076923077
kProd instance d=3 L=5 tau=4 a=(0,1,2): K=8.031420e-03, bound C*min(1,tau^-1.5)*exp(-c*min(n^2/tau,n)) = 2.560871e+05 (C=2.097e+06, c=0.010417, n=3)
```

What the script covers: `SB` built from the definition of `sbKernel` (identity or `zdistD = 1`), `1-tS = e + γΣΔ_j` asserted entrywise,
`Θ = (1 - tS)⁻¹` by `numpy.linalg.inv`; `hkT` from its definition (`HeatKernel1D.lean:133`); Laplace integral by 400 panels × 40-point
Gauss–Legendre on `[0, 40/e]` at `a ∈ {0, e₁, (1,..,1), (⌊L/2⌋,1,..)}`, `d ∈ {2,3}`, `L ∈ {3,4,5}`, `g ∈ {0.3,1,2}`, `t ∈ {0,0.5,0.95}`
(max error above, over all 54 parameter points). Bound pins: all `a ∈ Z_L³`, all `i, j`, `τ` on 14-point geometric grids
`[10⁻³, L²]` and `[L², 6L²]` (the grid stops at `6L²` because beyond that `e^{-4τ/L²}` is below double-precision rounding of `K - L^{-d}`).
Instance data (all hypotheses at once): `Theta_eq_laplace_prod` at `d=3, L=3, g=1, t=1/2, a=0` (`3 ≤ L`, `0 < g`, `0 ≤ t < 1` hold; `γ = 1/14`,
`e = 1/2`, both nonzero; `Θ(0,0) = 1.1230769…`); `sum_min_ge` at `d=3, x=(1,50,0), τ=10` (`0 < τ`, `x ≥ 0`: `17 ≤ 50.1`); `kProd_le` at
`d=3, L=5, τ=4` (`0 < τ ≤ 25`; `K = 8.03·10⁻³` at `a = (0,1,2)`, below the bound). No external hypothesis (no TEAM §8 lesson-14 limit needed): every
input is a merged theorem (`hkT_*`, `norm_SB`, `eq_Theta_of_mul`).

Route note (math only): route (a) is closed. Fourier: `χ_k` diagonalises the circulant `S` with symbol row 2; per mode `x⁻¹ = ∫₀^∞ e^{-sx}ds`;
`L^{-d}Σ_{k∈Z_L^d} ∏_j cos(2πk_ja_j/L)e^{-2γs(1-cos(2πk_j/L))} = ∏_j hkT L (γs) a_j` (the sine parts cancel under `k ↦ -k`, already built into the cosine
form of `hkT`). Then `eq_Theta_of_mul` with `B(x,y) = ∫ e^{-es}K_{γs}(y - x)ds` and `hS = norm_SB`.

### Verdicts

- `Theta_eq_laplace_prod` (LaplaceProd): PASS
- `sum_min_ge` (SumMin): PASS
- `kProd_le` (KProdBound): PASS
- `kProd_diff1_le` (KProdDiff1): PASS
- `kProd_diff2_le` (KProdDiff2): PASS
- `kProd_gap` (KProdGap): PASS

Overall verdict: PASS

## (a′) Preflight corrections — Sat Oct  3 03:58:34 UTC 2026

- Row 17 of (i): `f_τ(n) = min(n²/τ, n)` has `f_τ' = 2n/τ` on `[0, τ]` (reaching `2` at `n = τ`) and `1` beyond, not `min(2n/τ, 1)`;
  `f_τ` is 2-Lipschitz, so a unit shift of `n` costs at most `2` (the ticket's number), not `1`. No verdict changes. The Lean proof
  (`f_shift`) proves the loss `3` (three-case argument), hence `A = max(C₀,C₁,C₂)·e^{3c*}` in place of `C₂C₀^{d-1}e^{c*}`.
- Rows 19–20: the gap constant in the file is `d(1+C)^d` (coarser than the table's `d·C(1+C)^{d-1}`); the pins only ask `∃ C`. No verdict changes.

## (b) Script output — Sat Oct  3 03:58:34 UTC 2026

### b1 builds (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2019`, branch `t/T2019`)
```
$ lake build RBM3D.Propagator.HeatProduct 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
Build completed successfully (3401 jobs).
$ # root `RBM3D.lean` is not writable here: import added temporarily after `import RBM3D.Path.Walk`, full build, file restored
$ sed -i '' 's/^import RBM3D.Path.Walk$/import RBM3D.Path.Walk\nimport RBM3D.Propagator.HeatProduct/' RBM3D.lean; lake build > fullbuild.txt 2>&1; echo "exit $?"; cp RBM3D.lean.bak RBM3D.lean
$ tail -4 fullbuild.txt     (of the run made in this session, 3715 jobs, includes `#assert_rbm_axioms`)
 RBM.Gauss.Sizes.locDomain].
non-vacuity certificates: 6 of 13 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3715 jobs).
exit 0
$ git status --short   (after restoring RBM3D.lean and committing)
(empty)
```

### b2 axioms (`lake env lean axioms.lean`, file = `import RBM3D.Propagator.HeatProduct` + `#print axioms`)
```
'RBM.Heat.Theta_eq_laplace_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.sum_min_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.kProd_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.kProd_diff1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.kProd_diff2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.kProd_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.kProd' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|axiom" RBM3D/Propagator/HeatProduct.lean ; echo "grep exit $?"
grep exit 1
```

### b3 commit and scope
```
$ git log -1 --format="%h %an <%ae>  %s" ; git diff --stat main...t/T2019
ee4e9f9 Jun Yin <321276894+JYin80@users.noreply.github.com>  T2019: PT-D Laplace-product representation of Theta_t, 1/d sum-of-minima lemma, product-kernel bounds and gap
 RBM3D/Propagator/HeatProduct.lean | 1257 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1257 insertions(+)
```

### b4 pins against the check file `docs/tickets/checks/T2019-check.lean` (script diff + Lean)
```
$ python3 pindiff.py   (whitespace-normalised: check-file `def X : Prop :=` body vs the theorem type; `kProd` definition line)
LaplaceProd <-> Theta_eq_laplace_prod IDENTICAL
SumMin <-> sum_min_ge IDENTICAL
KProdBound <-> kProd_le IDENTICAL
KProdDiff1 <-> kProd_diff1_le IDENTICAL
KProdDiff2 <-> kProd_diff2_le IDENTICAL
KProdGap <-> kProd_gap IDENTICAL
kProd def <-> IDENTICAL
$ lake env lean pincheck.lean; echo "lean exit $?"   (check file with `import RBM3D.Propagator.HeatProduct`, its own `kProd` removed,
$                                                     `#check` lines removed, plus the six lines below inside its namespace)
example : LaplaceProd := Theta_eq_laplace_prod      example : SumMin := sum_min_ge      example : KProdBound := kProd_le
example : KProdDiff1 := kProd_diff1_le      example : KProdDiff2 := kProd_diff2_le      example : KProdGap := kProd_gap
lean exit 0
```

### b5 target statements, extracted from the file by script (`python3 extract.py`)
```lean
theorem Theta_eq_laplace_prod :
    ∀ (d L : ℕ) (hL : 3 ≤ L) (g t : ℝ), 0 < g → 0 ≤ t → t < 1 → ∀ a : Zd d L,
    haveI : NeZero L := ⟨by omega⟩
    Theta d L g (t : ℂ) 0 a =
      ((∫ s in Ioi (0 : ℝ), Real.exp (-(1 - t) * s) * kProd d L (lgGam d g t * s) a : ℝ) : ℂ)

theorem sum_min_ge : ∀ d : ℕ, 1 ≤ d → ∀ τ : ℝ, 0 < τ → ∀ x : Fin d → ℝ, (∀ j, 0 ≤ x j) →
    (d : ℝ)⁻¹ * min ((∑ j, x j) ^ 2 / τ) (∑ j, x j) ≤ ∑ j, min (x j ^ 2 / τ) (x j)

theorem kProd_le : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ a : Zd d L,
      kProd d L τ a ≤ C * min 1 (τ ^ (-(d : ℝ) / 2))
        * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ))

theorem kProd_diff1_le : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (j : Fin d),
      |kProd d L τ (a + Pi.single j 1) - kProd d L τ a| ≤ C * min 1 (τ ^ (-((d : ℝ) + 1) / 2))
        * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ))

theorem kProd_diff2_le : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (i j : Fin d),
      |kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
          - kProd d L τ (a + Pi.single j 1) + kProd d L τ a|
        ≤ C * min 1 (τ ^ (-((d : ℝ) + 2) / 2))
          * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ))

theorem kProd_gap : ∀ d : ℕ, 1 ≤ d → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ (a : Zd d L) (i j : Fin d),
      |kProd d L τ a - ((L : ℝ) ^ d)⁻¹| ≤ C * ((L : ℝ) ^ d)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
      |kProd d L τ (a + Pi.single j 1) - kProd d L τ a|
        ≤ C * ((L : ℝ) ^ (d + 1))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
      |kProd d L τ (a + Pi.single i 1 + Pi.single j 1) - kProd d L τ (a + Pi.single i 1)
          - kProd d L τ (a + Pi.single j 1) + kProd d L τ a|
        ≤ C * ((L : ℝ) ^ (d + 2))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2)

noncomputable def kProd (d L : ℕ) [NeZero L] (τ : ℝ) (a : Zd d L) : ℝ := ∏ j, hkT L τ (a j)
```

### b6 compiled instances (all seven `example`s compile; the three the ticket asks for are shown in full)
```lean
1194:example : Theta 3 3 1 (((1 / 2 : ℝ)) : ℂ) 0 0
1200:example : ((3 : ℕ) : ℝ)⁻¹ * min ((∑ j, (![1, 50, 0] : Fin 3 → ℝ) j) ^ 2 / 10)
1207:example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
1214:example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
1223:example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
1234:example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
1245:example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
-- `Theta_eq_laplace_prod` at `d = 3`, `L = 3`, `g = 1`, `t = 1/2`, `a = 0`
-- (`γ = 1/14`, `1 - t = 1/2`).
example : Theta 3 3 1 (((1 / 2 : ℝ)) : ℂ) 0 0
    = ((∫ s in Ioi (0 : ℝ), Real.exp (-(1 - 1 / 2) * s) * kProd 3 3 (lgGam 3 1 (1 / 2) * s) 0
        : ℝ) : ℂ) :=
  Theta_eq_laplace_prod 3 3 le_rfl 1 (1 / 2) one_pos (by norm_num) (by norm_num) 0

-- `sum_min_ge` at `d = 3`, `x = (1, 50, 0)`, `τ = 10`: `(1/3) * min (51²/10) 51 ≤ 0.1 + 50 + 0`.
example : ((3 : ℕ) : ℝ)⁻¹ * min ((∑ j, (![1, 50, 0] : Fin 3 → ℝ) j) ^ 2 / 10)
      (∑ j, (![1, 50, 0] : Fin 3 → ℝ) j)
    ≤ ∑ j, min ((![1, 50, 0] : Fin 3 → ℝ) j ^ 2 / 10) ((![1, 50, 0] : Fin 3 → ℝ) j) :=
  sum_min_ge 3 (by norm_num) 10 (by norm_num) ![1, 50, 0]
    (fun j => by fin_cases j <;> simp)

-- `kProd_le` at `d = 3`, `L = 5`, `τ = 4`, `a = (0, 1, 2)` (`|a| = 3`).
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    kProd 3 5 4 ![0, 1, 2] ≤ C * min 1 ((4 : ℝ) ^ (-((3 : ℕ) : ℝ) / 2))
      * Real.exp (-c * min ((zdistD 3 5 ![0, 1, 2] : ℝ) ^ 2 / 4) (zdistD 3 5 ![0, 1, 2] : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := kProd_le 3 (by norm_num)
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) _⟩
-- the other four: `exact` lines
1211:  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) _⟩
1219:  obtain ⟨C, c, hC, hc, h⟩ := kProd_diff1_le 3 (by norm_num)
1220:  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) _ 1⟩
1230:  obtain ⟨C, c, hC, hc, h⟩ := kProd_diff2_le 3 (by norm_num)
1231:  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) _ 0 2⟩
1241:  obtain ⟨C, c, hC, hc, h⟩ := kProd_diff2_le 3 (by norm_num)
1242:  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) _ 1 1⟩
1254:  obtain ⟨C, c, hC, hc, h⟩ := kProd_gap 3 (by norm_num)
1255:  exact ⟨C, c, hC, hc, h 5 50 (by norm_num) _ 0 2⟩
```

### b7 name clash and ports
```
$ for n in kProd Theta_eq_laplace_prod sum_min_ge kProd_le kProd_diff1_le kProd_diff2_le kProd_gap; do grep -rnw --include=*.lean "$n" RBM3D RBM3D.lean | grep -v HeatProduct.lean; done ; echo "hits above: none expected"
(end)
$ grep -n "RBM1D\|RBM2D" RBM3D/Propagator/HeatProduct.lean   (ports: none; only the docstring sentence saying nothing is copied)
45:`sum_cos_orth` of `HeatTorus1D.lean` / `HeatKernel1D.lean`.  Nothing is copied from `RBM1D` or
46:`RBM2D`.
```

Narrative (route and structure; every item is a statement about the file):
- `Theta_eq_laplace_prod` uses route (b) of the ticket. `hkT_hasDerivAt` differentiates the finite Fourier sum of `hkT` in `τ` and gives `∂_τ hk(x) = hk(x+1)+hk(x-1)-2hk(x)`;
  `kProd_hasDerivAt` (`HasDerivAt.fun_finsetProd`) gives `∂_τ K = Σ_p K(a+u_p) - 2d K`. `sum_kernel_mul` shows, from the definition of `sbKernelR` and the neighbour
  reindexing `sum_adj` (`filter_zdistD_eq_one`, `unitVec_injective`), `Σ_y K_τ(y-x)(δ_{yz} - t S_{yz}) = (1-t)K_τ(a) - lgGam·∂_τK_τ(a)`, `a = z-x`.
  `phi_integral` integrates `e^{-es}((1-t)K - γ∂_τK)` over `(0,∞)` by `integral_Ioi_of_hasDerivAt_of_tendsto` (limit `0` from `0 ≤ K ≤ 1`, value `K_0(a) = δ_{a,0}` from `hkT_zero`).
  `laplace_matrix` assembles `B(1 - tS) = 1` entrywise; `eq_Theta_of_mul` with `norm_SB` and `‖(t:ℂ)‖ < 1` gives `B = Theta`. No Fourier diagonalisation of `S` is used.
- `hkT_zero` needs the finite orthogonality of the characters; the lemmas in `HeatKernel1D.lean` are private, so `hp_sum_exp_orth`, `hp_sum_cos_orth`, `hp_cos_phase`, `hkT_rep` re-prove them in this file.
- `sum_min_ge`: if all `x_j ≤ τ`, Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`); otherwise `min(x²/τ,x) ≥ x/d - τ/(4d²)` for every coordinate and `= x_{j₀}` for the one with `x_{j₀} > τ`,
  which gives `Σ_j min(x_j²/τ,x_j) ≥ X/d` (stronger than the pin needs).
- Bounds: `factor_bounds` fixes one pair `(A, c)` for the three one-dimensional bounds (`c = min(c₀,c₁,c₂)`, `A = max(C₀,C₁,C₂)e^{3c}`); `prod_bound` gives
  `|∏F| ≤ A^d u^{Σn} e^{-(c/d)·min(X²/τ,X)}` with `u = min(1,τ^{-1/2})` from `sum_min_ge`; `u^n = min(1,τ^{-n/2})` (`hpU_pow`). `kProd_diff1_le`: one factor differenced (`n = d+1`);
  `kProd_diff2_le`: `i ≠ j` two factors differenced (`kProd_two`), `i = j` the factor `hk(x+2)-2hk(x+1)+hk(x)` is `hkT_diff2_le` at `x+1` with the position shift of `min(n²/τ,n)` bounded by `f_shift`.
- `kProd_gap`: `abs_prod_sub_prod_le` (telescoping with absolute values, `|x_j|,|y_j| ≤ M`) for `|K - L^{-d}|`; `gap_prod` for the two difference bounds; the factor bounds come from `hkT_gap`.
  The bound pins hold for every `[NeZero L]`; only `Theta_eq_laplace_prod` uses `3 ≤ L` (for `norm_SB`, `filter_zdistD_eq_one`, `unitVec_injective`).
- No new hypothesis `Prop`, no `structure`, no axiom; helpers are `private`; the only public names are `kProd` and the six pinned theorems.

## (c) Verified Mathlib names (all `#check`ed in `names.lean`, no errors; Mathlib `v4.34.0`)
`HasDerivAt.fun_finsetProd`, `HasDerivAt.fun_sum`, `HasDerivAt.exp`, `HasDerivAt.comp`, `HasDerivAt.mul`, `HasDerivAt.congr_deriv`, `integral_Ioi_of_hasDerivAt_of_tendsto`,
`exp_neg_integrableOn_Ioi`, `MeasureTheory.integral_finsetSum`, `MeasureTheory.integrable_finsetSum`, `MeasureTheory.integral_mul_const`, `MeasureTheory.integral_neg`,
`MeasureTheory.setIntegral_congr_fun`, `MeasureTheory.Integrable.mono'`, `MeasureTheory.ae_restrict_iff'`, `Real.tendsto_exp_neg_atTop_nhds_zero`,
`tendsto_of_tendsto_of_tendsto_of_le_of_le'`, `sq_sum_le_card_mul_sum_sq`, `Finset.prod_le_prod₀` (semiring version, takes `h0` and `h1`), `Finset.prod_le_one₀`, `Finset.prod_nonneg`,
`Finset.mul_prod_erase`, `Finset.abs_prod`, `Finset.prod_pow_eq_pow_sum`, `Real.exp_sum`, `pow_le_of_le_one`, `one_le_pow₀`, `pow_le_one₀`, `Fintype.sum_equiv`, `Finset.sum_image`,
`Finset.sum_filter`, `Fintype.sum_prod_type`, `Fintype.sum_bool`, `Finset.card_insert_of_notMem`, `ZMod.val_one_eq_one_mod`, `AddChar.sum_mulShift`, `ZMod.isPrimitive_stdAddChar`,
`ZMod.stdAddChar_coe`, `ZMod.intCast_zmod_eq_zero_iff_dvd`, `Real.cos_add_int_mul_two_pi`, `Complex.exp_ofReal_mul_I_re`, `Matrix.mul_apply`.
Not usable as written in this Mathlib (seen in the tool log): `HasDerivAt.finset_prod` (deprecated alias of `finsetProd`); `Finset.prod_le_prod` and `Finset.prod_le_one` are the ordered-monoid versions without
nonnegativity hypotheses, the real-number versions are `prod_le_prod₀`, `prod_le_one₀`; `Finset.prod_le_pow_card` needs `MulLeftMono ℝ` (instance fails). Deprecated, with the replacement named by the warning:
`if_true` -> `ite_true`, `if_false` -> `ite_false`, `if_neg` -> `ite_eq_right`, `ite_cond_eq_false` -> `ite_eq_right_of_eq_false`, `push_neg` -> `push Not`, `MeasureTheory.integral_finset_sum` -> `integral_finsetSum`.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. The six statements equal the pins (b4); no Lean/paper statement difference was introduced.
- Hub step at merge: add `import RBM3D.Propagator.HeatProduct` after the last `import` of `RBM3D.lean` (tested above by a temporary edit, restored).
- The constants `C, c` of the four bounds depend on `d` and on the obtained one-dimensional constants only; no numerical value is recorded. Preflight (ii) numerics were not rerun.
- `docs/mathlib-api.md` additions: the names in (c).

