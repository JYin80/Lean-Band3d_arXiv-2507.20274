Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 02:19:40 UTC 2026

### (i) Exponent table

Notation: `m(n) = min(n²/τ, |n|)`; `x̂ ∈ ℤ` the representative of `x ∈ ℤ_L` with `|x̂| = zdist L x ≤ L/2`;
`s = τ/L²`; `j = min(k, L−k)`. Merged constants (read from the `refine ⟨…⟩` of `hkZ_le`, `hkZ_diff1_le`,
`hkZ_diff2_le` in `RBM3D/Propagator/HeatBounds1D.lean`): `(C_Z,c_Z) = (1, 1/8)`, `(12.4248, 1/16)`, `(517.029, 1/16)`
for (a), (b), (c) (printed below). Prover must take them from the existential by `obtain`, not hard-code.

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| shift of image index | `x.val = x̂ + L·t`, `t ∈ {0,1}` (`t=1` iff `2·x.val > L`) | `y ↦ y + t` bijection of ℤ preserves `HasSum`; `(x±1)` has representative `x̂±1`, so the three images sums share `x̂+Ly` | exact |
| geometry, `y ≠ 0` | `|x̂+Ly| ≥ L|y| − L/2 ≥ L|y|/2`; `≥ L/2 ≥ |x̂|` | `|x̂| ≤ L/2`, `L ≥ 1`, `|y| ≥ 1` | exact (L=1,2 included: `zdist 2 1 = 1 = L/2`) |
| monotonicity | `m` nondecreasing in `|n|`, so `m(x̂+Ly) ≥ m(x̂)` | `min` of two nondecreasing maps | exact |
| per-image gain | `m(x̂+Ly) ≥ min(L²y²/(4τ), L|y|/2) ≥ |y|/4` | `τ ≤ L²`: `L²/(4τ) ≥ 1/4`; `L ≥ 1`: `L/2 ≥ 1/2`; `y² ≥ |y|` | factor ≥ 1 in the first, 2 in the second |
| split of exponent | `e^{-c m(n)} ≤ e^{-(c/2) m(x̂)} e^{-c|y|/8}` | `m(n) ≥ m(x̂)` and `m(n) ≥ |y|/4` | exact |
| y-series | `S(c) = 1 + 2 Σ_{y≥1} e^{-c|y|/8} = 1 + 2/(e^{c/8} − 1)` | `c > 0` | finite for every `c > 0` |
| (a) torus constants | `c_T = c_Z/2 = 1/16`, `C_T = C_Z·S(1/8) = 256.0013` (take `C = 257`) | the factor `min 1 τ^{-1/2}` passes termwise | printed sup ratio 0.0040 at these constants |
| (b) torus constants | `c_T = 1/32`, `C_T = 12.4248·S(1/16) = 6361.5` (take `6362`) | termwise, `min 1 τ⁻¹` passes | sup ratio 1.6e-4 |
| (c) torus constants | `c_T = 1/32`, `C_T = 517.03·256.0 = 264719.3` (take `264720`) | termwise, `min 1 τ^{-3/2}` passes | sup ratio 7.8e-6 |
| difference terms | `Δ₁hk(x) = Σ_y [h(x̂+1+Ly) − h(x̂+Ly)]`, `Δ₂` likewise; `hkZ_diff*_le` applied at `n = x̂+Ly` gives `e^{-c m(n)}`, the same exponent as for `h` | no `x̂±1` shift of `m` is needed (the pin has `zdist x`) | exact |
| zero mode (τ ≥ L²) | `k = 0` term `= 1/L` (`cos 0 · e^0`) | — | exact; `L=1`: `hk = 1 = 1/L` |
| Jordan | `1 − cos(2πk/L) ≥ 8 j²/L²` (`sin u ≥ 2u/π` on `[0,π/2]`, `u = πj/L ≤ π/2`) | `j ≤ L/2`; `cos` symmetric under `k ↔ L−k` | constant 8 attained at `j = L/2`; checked `L < 200` below |
| gap exponent | `e^{-2τ(1−cos)} ≤ e^{-16 s j²}` | `s ≥ 1` | — |
| gap sums, `s ≥ 1`, `p=0,1,2` | `Σ_{j≥1} j^p e^{-16 s j²} ≤ e^{-8s} Σ_{j≥1} j^p e^{-8j²} ≤ 3.36·10⁻⁴ e^{-8s}` | `16 s j² = 8 s j² + 8 s j² ≥ 8 s + 8 j²` for `s,j ≥ 1` | `Σ j^p e^{-8j²} = 3.3546·10⁻⁴` (j=1 term, remainder < 10⁻¹³); easy bound `j^p e^{-8j²} ≤ e^{-7j²}` no loss in practice |
| (d0) `|hk − 1/L|` | `≤ L⁻¹ · 2 Σ_j e^{-16 s j²} ≤ 2.0001 L⁻¹ e^{-16 s}` (each `j` hit by ≤ 2 values of `k`) | take `C = 3`, `c = 4`; `e^{-16s} ≤ e^{-4s}` | factor 1.5 in C, 12 in the exponent |
| (d1) `|Δ₁hk|` | `|cos a − cos b| ≤ |a−b| = 2πj/L`; `≤ L⁻¹ (2π/L) · 2 · 3.36e-4 e^{-8s} = 0.0043 L⁻² e^{-8s}` | `C = 3`, `c = 4` (`e^{-8s} ≤ e^{-4s}`); `k = 0` term cancels | factor ~700 in C, 2 in the exponent |
| (d2) `|Δ₂hk|` | `cos(a(x+1)) + cos(a(x−1)) − 2cos(ax) = 2cos(ax)(cos a − 1)`, `|·| ≤ a² = 4π²j²/L²`; total `≤ 0.0265 L⁻³ e^{-8s}` | `C = 3`, `c = 4` | factor ~110 in C, 2 in the exponent |
| uniform gap pair | `(C, c) = (3, 4)` serves all three lines of `TorusGap` | — | see slack columns |

Index remark: `hkT` uses `val`; `cos(2πk·(x+1).val/L) = cos(2πk(x.val+1)/L)` because `k·L/L ∈ ℤ` (periodicity), so no wrap-around case split is needed in the gap part.

### (ii) Concrete nondegenerate instance and script check

Instance: `L = 5` (`NeZero 5`), `x = 2` (`zdist 5 2 = 2`), `τ = 4 ≤ 25 = L²` for (a)–(c), `τ = 50 ≥ 25` for `TorusGap`. All hypotheses (`0 < τ`, `τ ≤ L²` resp. `L² ≤ τ`) hold; no external hypothesis.
Command (pure Python, no Lean; script kept in the scratchpad): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/pf.py`
Output (verbatim):

```
C_Z,c_Z: (1, 0.125) (12.42477796076938, 0.0625) (517.0291954002568, 0.0625)
torus (C,c) a,b,c: [(256.0013020820088, 0.0625), (6361.494404960016, 0.03125), (264719.28465239494, 0.03125)]
geometry holds: True ; worst image-sum ratio (<=1): 0.12504005146769218
sup ratios LHS/RHS (a,b,c) with derived constants (<=1 needed): [0.003967744305696132, 0.00016169995043594122, 7.763882243573466e-06]
gap ratios (C=3,c=4): [2.048070784718625e-06, 8.1922831388745e-06, 3.2769132555498e-05]
Jordan 1-cos(2pi k/L)>=8 min(k,L-k)^2/L^2, L<200: True
p=0 sum_j j^p e^{-8j^2} = 3.354626e-04
p=1 sum_j j^p e^{-8j^2} = 3.354626e-04
p=2 sum_j j^p e^{-8j^2} = 3.354626e-04
p=0 sup_s sum_j j^p e^{-16 s j^2}/e^{-8s} (s>=1) = 3.354626e-04
p=1 sup_s sum_j j^p e^{-16 s j^2}/e^{-8s} (s>=1) = 3.354626e-04
p=2 sup_s sum_j j^p e^{-16 s j^2}/e^{-8s} (s>=1) = 3.354626e-04
gap consts: |hk-1/L|<=2.000000/L e^{-16s}; |D1|<=0.004216/L^2 e^{-8s}; |D2|<=0.026487/L^3 e^{-8s}
L=5 tau=4 x=2: zdist=2 hk=1.987139e-01 D1=0.000000e+00 D2=1.777205e-03
L=5 tau=50 x=2: zdist=2 hk=2.000000e-01 D1=0.000000e+00 D2=0.000000e+00
 pin a LHS=1.9871e-01 RHS=1.2025e+02
 pin b LHS=0.0000e+00 RHS=1.5414e+03
 pin c LHS=1.7772e-03 RHS=3.2072e+04
 gap LHS/RHS: 0.0 0.0 0.0
```

Reading: pins (a),(b),(c) at `L ∈ {1,2,3,4,5,7,16,64}`, all `x`, `τ ∈ [10⁻³, L²]`, with the derived constants `(257, 1/16)`, `(6362, 1/32)`, `(264720, 1/32)`: sup LHS/RHS ≤ 0.004; gap with `(3,4)`, `τ ∈ [L², 30L²]`: sup ratio ≤ 3.3e-5. At `L=5, x=2` the first difference is exactly 0 by the symmetry `hk(3) = hk(2)` (`x+1 ≡ −2`); the instance is still nondegenerate (hk > 0, `Δ₂ ≠ 0`).

### Verdicts

- `hkT_le` (TorusBound): PASS. Image-sum geometry, series `S(c)` and merged `hkZ_le` close; no obstruction.
- `hkT_diff1_le` (TorusDiff1): PASS (termwise via `hkZ_diff1_le`; same geometry).
- `hkT_diff2_le` (TorusDiff2): PASS (termwise via `hkZ_diff2_le`; same geometry).
- `hkT_gap` (TorusGap): PASS. Jordan, zero mode, and `Σ j^p e^{-16 s j²}` tails close with `(C,c) = (3,4)`.


## (b) Script output — Sat Oct  3 03:08:40 UTC 2026

Commit on `t/T2017`: `c6a31ce`; the sole file is `RBM3D/Propagator/HeatTorus1D.lean` (the first block below).

```
$ git log --oneline main..t/T2017; git diff --stat main...t/T2017
c6a31ce T2017: PT-C bounds of the 1D heat kernel on the torus Z_L
 RBM3D/Propagator/HeatTorus1D.lean | 760 ++++++++++++++++++++++++++++++++++++++
 1 file changed, 760 insertions(+)

$ wc -l RBM3D/Propagator/HeatTorus1D.lean; grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Propagator/HeatTorus1D.lean
     760 RBM3D/Propagator/HeatTorus1D.lean
0

$ lake env lean RBM3D/Propagator/HeatTorus1D.lean; echo EXIT=$?
EXIT=0

$ lake build RBM3D.Propagator.HeatTorus1D 2>&1 | tail -5
Build completed successfully (3390 jobs).

$ lake env lean axioms.lean   (import RBM3D.Propagator.HeatTorus1D; #print axioms of the four theorems)
'RBM.Heat.hkT_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkT_diff1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkT_diff2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkT_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full library build (root `#assert_rbm_axioms`; the root file is not writable here, so the second build adds the module import temporarily and reverts it):

```
$ lake build   (RBM3D.lean untouched on the branch; root #assert_rbm_axioms runs)
non-vacuity certificates: 6 of 13 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3699 jobs).

$ python3: temporarily add "import RBM3D.Propagator.HeatTorus1D" after the last import of RBM3D.lean; lake build; git checkout RBM3D.lean
 RBM3D.lean | 1 +
 1 file changed, 1 insertion(+)
non-vacuity certificates: 6 of 13 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3701 jobs).
Updated 1 path from the index
$ git status --short   (after the revert)
(empty = clean)
```

Pins against theorem types, and the target statements (extracted from the file):

```
$ python3 (extract pin bodies from docs/tickets/checks/T2017-check.lean and theorem types from RBM3D/Propagator/HeatTorus1D.lean, compare after whitespace normalisation)
TorusBound vs hkT_le : identical = True
TorusDiff1 vs hkT_diff1_le : identical = True
TorusDiff2 vs hkT_diff2_le : identical = True
TorusGap vs hkT_gap : identical = True

$ lake env lean pins.lean   (the four pins copied from the check file; theorem p1 : TorusBound := hkT_le, ... p4)
EXIT=0

$ python3 (print each target theorem statement from the file, up to ":= by")
theorem hkT_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
    ∀ x : ZMod L,
      hkT L τ x ≤ C * min 1 (τ ^ (-(1 / 2 : ℝ)))
        * Real.exp (-c * min ((RBM.zdist L x : ℝ) ^ 2 / τ) (RBM.zdist L x : ℝ)) := by

theorem hkT_diff1_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ →
    τ ≤ (L : ℝ) ^ 2 → ∀ x : ZMod L,
      |hkT L τ (x + 1) - hkT L τ x| ≤ C * min 1 τ⁻¹
        * Real.exp (-c * min ((RBM.zdist L x : ℝ) ^ 2 / τ) (RBM.zdist L x : ℝ)) := by

theorem hkT_diff2_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ →
    τ ≤ (L : ℝ) ^ 2 → ∀ x : ZMod L,
      |hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x|
        ≤ C * min 1 (τ ^ (-(3 / 2 : ℝ)))
          * Real.exp (-c * min ((RBM.zdist L x : ℝ) ^ 2 / τ) (RBM.zdist L x : ℝ)) := by

theorem hkT_gap : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ →
    ∀ x : ZMod L,
    |hkT L τ x - (L : ℝ)⁻¹| ≤ C * (L : ℝ)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
    |hkT L τ (x + 1) - hkT L τ x| ≤ C * ((L : ℝ) ^ 2)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
    |hkT L τ (x + 1) + hkT L τ (x - 1) - 2 * hkT L τ x|
      ≤ C * ((L : ℝ) ^ 3)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) := by
```

Compiled instances, name-clash and port greps:

```
$ awk (print from "### Compiled instances" to the end of RBM3D/Propagator/HeatTorus1D.lean); the examples are part of the file built above
/-! ### Compiled instances

Each target theorem applied at `L = 5`, `x = 2` (`|x|_L = 2`): `τ = 4 ≤ 25 = L²` for the three
bounds and `τ = 50 ≥ 25 = L²` for the gap.  Every deterministic hypothesis is discharged; the
constants stay existential, as in the statements. -/

-- `hkT_le` at `L = 5`, `τ = 4`, `x = 2`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    hkT 5 4 2 ≤ C * min 1 ((4 : ℝ) ^ (-(1 / 2 : ℝ)))
      * Real.exp (-c * min ((RBM.zdist 5 2 : ℝ) ^ 2 / 4) (RBM.zdist 5 2 : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkT_le
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) 2⟩

-- `hkT_diff1_le` at `L = 5`, `τ = 4`, `x = 2`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |hkT 5 4 (2 + 1) - hkT 5 4 2| ≤ C * min 1 ((4 : ℝ)⁻¹)
      * Real.exp (-c * min ((RBM.zdist 5 2 : ℝ) ^ 2 / 4) (RBM.zdist 5 2 : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkT_diff1_le
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) 2⟩

-- `hkT_diff2_le` at `L = 5`, `τ = 4`, `x = 2`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |hkT 5 4 (2 + 1) + hkT 5 4 (2 - 1) - 2 * hkT 5 4 2|
      ≤ C * min 1 ((4 : ℝ) ^ (-(3 / 2 : ℝ)))
        * Real.exp (-c * min ((RBM.zdist 5 2 : ℝ) ^ 2 / 4) (RBM.zdist 5 2 : ℝ)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkT_diff2_le
  exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) 2⟩

-- `hkT_gap` at `L = 5`, `τ = 50`, `x = 2`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (|hkT 5 50 2 - ((5 : ℕ) : ℝ)⁻¹|
        ≤ C * ((5 : ℕ) : ℝ)⁻¹ * Real.exp (-c * 50 / ((5 : ℕ) : ℝ) ^ 2) ∧
      |hkT 5 50 (2 + 1) - hkT 5 50 2|
        ≤ C * (((5 : ℕ) : ℝ) ^ 2)⁻¹ * Real.exp (-c * 50 / ((5 : ℕ) : ℝ) ^ 2) ∧
      |hkT 5 50 (2 + 1) + hkT 5 50 (2 - 1) - 2 * hkT 5 50 2|
        ≤ C * (((5 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-c * 50 / ((5 : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkT_gap
  exact ⟨C, c, hC, hc, h 5 50 (by norm_num) 2⟩

end RBM.Heat

$ grep -rn "hkT_le\b\|hkT_diff1_le\|hkT_diff2_le\|hkT_gap" RBM3D --include="*.lean" | grep -v "^RBM3D/Propagator/HeatTorus1D.lean"   # name clash with the other modules
(no output above = no clash)

$ grep -rnE "(lemma|theorem|def|abbrev) (<name>)\b" RBM3D --include="*.lean" | grep -v HeatTorus1D   # for the 19 private helper names
names: exists_rep hasSum_images_rep summable_exp_abs image_geometry image_term_le torus_abs_le exists_rep_real shift_fun shift_fun' mul_exp_neg_le_one jordan_nat jordan_torus sum_geom_zdist ang tail_sum mode_bounds cos_phase hkT_form erase_sum_bound
(no output above = no public declaration of the same name elsewhere; the 19 helpers are private)

$ grep -n "^theorem\|^lemma\|^def\|^noncomputable def" RBM3D/Propagator/HeatTorus1D.lean   (public declarations of the file)
218:theorem hkT_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 →
240:theorem hkT_diff1_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ →
266:theorem hkT_diff2_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 < τ →
608:theorem hkT_gap : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ →

$ grep -c "^private" RBM3D/Propagator/HeatTorus1D.lean
19

$ grep -n "RBM1D\|RBM2D" RBM3D/Propagator/HeatTorus1D.lean   (ports from the sister projects)
(no match = no text copied from the sister projects)
```

### Narrative

- At the start of this run the head of `t/T2017` was 868b3b4 (an ancestor of `main`, no commit of its own) and `git status` was clean, so the module was written from scratch against the ticket and section (a). No correction to (a) is needed, so there is no (a′).
- `τ ≤ L²`: `exists_rep_real` gives the representative `a` of `x` with `|a| = zdist L x` and `2|a| ≤ L`; `hasSum_images_rep` reindexes `hkT_hasSum_images` by `Equiv.addRight` to any integer representative (used for `a`, `a + 1`, `a - 1`, so `Δ₁`, `Δ₂` are image sums of `hkZ(n+1) - hkZ n` and `hkZ(n+1) + hkZ(n-1) - 2 hkZ n` at `n = a + L y`).
- `image_geometry`/`image_term_le`: for `y ≠ 0`, `|n| ≥ L|y| - |a| ≥ max(|a|, L|y|/2)`, hence `m(n) ≥ m(a)` and `m(n) ≥ |y|/4` (`τ ≤ L²`, `L ≥ 1`), so `e^{-c m(n)} ≤ e^{-(c/2) m(a)} e^{-(c/8)|y|}`; `torus_abs_le` sums this with `HasSum.norm_le_of_bounded`.
- The three bounds take `(C_Z, c_Z)` from `obtain` on `hkZ_le`, `hkZ_diff1_le`, `hkZ_diff2_le` and use `C = C_Z * K`, `c = c_Z / 2` with `K = ∑' y : ℤ, exp(-(c_Z/8)|y|)` (only shown positive, `Summable.tsum_pos`). This is the preflight's `S(c_Z) = 1 + 2/(e^(c_Z/8) - 1)` left unevaluated, so the preflight's numeric `C_T` (257, 6362, 264720) is not in Lean; the statements are existential, as pinned.
- `τ ≥ L²` follows a different route from the preflight's `Σ j^p e^(-16 s j²)` sums. With `q_k = 1 - cos(2πk/L)`, `w_k = e^(-τ q_k)`: `mode_bounds` uses only `t e^(-t) ≤ 1` (`mul_exp_neg_le_one`), `|cos(u+a) - cos u| ≤ q + |sin a|`, `sin² a ≤ 2q`, `cos(u+a) + cos(u-a) - 2 cos u = -2 q cos u`, and gives `|cos u E| ≤ w`, `|Δ₁ term| ≤ 2 w / L`, `|Δ₂ term| ≤ 2 w / L²` for `τ ≥ L²` (`E = e^(-2τ q) = w²`).
- The `k = 0` term is `1/L` (`Finset.add_sum_erase`) and cancels in the differences (`Finset.sum_erase`); the phase of `(x ± 1).val` is replaced by `x.val ± 1` through `cos_phase` (`ZMod.intCast_zmod_eq_zero_iff_dvd`, `Real.cos_add_int_mul_two_pi`), so there is no wrap-around case split.
- Tail: `jordan_torus` (`1 - cos(2πk/L) ≥ 8 |k|_L² / L²`, from `Real.mul_le_sin` and `cos 2θ = 1 - 2 sin² θ`), then `e^(-τ q_k) ≤ e^(-4τ/L²) r^(|k|_L)` with `r = e^(-4) ≤ 1/5` (using `4 s + 4 j ≤ 8 s j²` for `s = τ/L² ≥ 1`, `j ≥ 1`), and `sum_geom_zdist` (`Σ_(k≠0) r^(|k|_L) ≤ 2 r/(1-r) ≤ 1/2`). The result is `(C, c) = (1, 4)`.
- The proofs are uniform in `L` (`NeZero L`), so `L = 1, 2` need no separate case; the instances are at `L = 5`, `x = 2` (`zdist 5 2 = min 2 3 = 2` by the definition in `RBM3D/Defs/Lattice.lean:25`), `τ = 4` for the three bounds (so `min(x²/τ, |x|) = 1`) and `τ = 50` for the gap; every hypothesis is discharged by `norm_num`, there is no external hypothesis.
- No new hypothesis `Prop`, no change of a pin; 19 helpers are `private` (one `private noncomputable def ang`); `RBM3D.lean` and `RBM3D/Test/Axioms.lean` are not in the commit.
- No text was taken from `../RBM1D` or `../RBM2D` (grep above); the required-reading file `../RBM2D/RBM2D/Propagator/PeriodizeImageSum.lean` was not opened, so there is no port and no diff-stat to give.
- Preflight section (a) was not rerun; its script output is its own.

## (c) Verified Mathlib names

Checked by `#eval` with `Lean.Environment.contains` in a scratch file importing `RBM3D.Propagator.HeatTorus1D` (every name below printed `true`; a grep of each last component in the file finds at least one use):

```
Real.mul_le_sin, Real.cos_two_pi_sub, Real.cos_add_int_mul_two_pi, Real.cos_two_mul
Real.cos_sq', Real.sin_sq_add_cos_sq, Real.neg_one_le_cos, Real.cos_le_one
Real.abs_cos_le_one, Real.abs_sin_le_one, Real.add_one_le_exp, Real.exp_le_one_iff
Real.exp_lt_exp, Real.exp_nat_mul, Real.exp_neg, Real.exp_add, Real.cos_add, Real.cos_sub
HasSum.norm_le_of_bounded, Summable.of_nat_of_neg, Summable.tsum_pos
summable_geometric_of_lt_one, geom_sum_Ico_le_of_lt_one, Equiv.hasSum_iff, ZMod.neg_val
ZMod.val_pos, ZMod.val_injective, ZMod.val_lt, ZMod.natCast_zmod_val, ZMod.natCast_self
ZMod.intCast_zmod_eq_zero_iff_dvd, Finset.sum_erase, Finset.add_sum_erase, Finset.sum_image
Finset.sum_le_sum_of_subset_of_nonneg, Finset.abs_sum_le_sum_abs, Finset.sum_sub_distrib
Finset.sum_add_distrib, sq_le_sq₀, inv_anti₀, one_le_div, div_le_div_of_nonneg_right
div_le_div_of_nonneg_left, one_div_le_one_div_of_le, inv_le_one_of_one_le₀, pow_le_pow_left₀
div_le_div_iff₀, div_le_iff₀, div_le_one, Int.one_le_abs, abs_sub_comm, abs_sub
Real.rpow_nonneg
```

Verified absent: `Real.exp_lt_one` (printed `false`; `Real.exp_lt_exp` is used instead).

## (d) Open issues and paper-delta candidates

- No open issue. No paper-delta candidate (`T2017a` etc.): the four statements are exactly the ticket's pins.
- For PT-D: `hkT_le`, `hkT_diff1_le`, `hkT_diff2_le` expose existential constants only (`C_T = C_Z K`, `c_T = c_Z / 2`); `hkT_gap` is existential in `(C, c)` too (the proof gives `(1, 4)`).
