Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 00:14:02 UTC 2026

### (i) Exponent table

Notation: `h_τ(n) = hkZ τ n = e^{-2τ} Σ_j τ^j N_j(n)/j!`; `N_j(n) = #{ε ∈ {±1}^j : Σε = n}` (`walkCount`).

| Quantity | Value | Constraint it must satisfy | Slack |
|---|---|---|---|
| `N_j(n)` support and value | `N_j(n) = C(j,(j+n)/2)` if `|n| ≤ j` and `j ≡ n (mod 2)`, else `0` | defines the series; `N_j(-n) = N_j(n)` (`k ↦ C(j,k) = C(j,j-k)`); brute force `j ≤ 10`, `|n| ≤ 12` in script below | exact |
| `N_j(n) ≤ 2^j` | `Σ_n N_j(n) = 2^j` (number of sequences) | gives `Σ_j |τ|^j N_j(n)/j! ≤ e^{2|τ|}`, so the tsum in `hkZ` is absolutely convergent for every real `τ` (needed for `Symm`, stated for all `τ`) | none needed (exact count) |
| double series | `Σ_n Σ_j |τ|^j N_j(n)|z|^n/j! = Σ_j |τ|^j (|z|+|z|^{-1})^j/j! = exp(|τ|(|z|+|z|^{-1}))` | finite for all `z ≠ 0`; justifies the Fubini swap in `MGF` (binomial `Σ_n N_j(n) z^n = (z+z^{-1})^j`) | finite for every `z ∈ ℂ\{0}`, no restriction |
| MGF | `Σ_n h_τ(n) z^n = e^{-2τ} e^{τ(z+z^{-1})}` | `τ ≥ 0` (pin), `z ≠ 0`; `z = 1` gives `e^{0} = 1` (mass one); `z = e^{iθ}` gives `exp(-2τ(1-cos θ))` | `z = 1`: exponent is exactly `0` |
| majorant of the tilted series | `Σ_m h_τ(m) e^{|ν||m|} ≤ Σ_m h_τ(m)(e^{νm}+e^{-νm}) = 2 e^{2τ(cosh ν − 1)}` (MGF at `z = e^{±ν}`, `e^{ν}+e^{-ν} = 2cosh ν`) | must be finite and independent of `k` to dominate `|h_τ(m) e^{(ν+ik)m} e^{-ikn}| = h_τ(m)e^{νm}`; needs `h_τ ≥ 0` (`τ ≥ 0`) | script: bound holds at `τ ∈ {.1,1,10}`, `ν ∈ {.5,1}`; integrated majorant over `[-π,π]` is `2π · 2e^{2τ(cosh ν -1)} < ∞` |
| `z` in `Tilt` | `z = e^{ν+ik}`, `z + z^{-1} = 2cosh(ν+ik)`; MGF gives `Σ_m h_τ(m)e^{(ν+ik)m} = exp(2τ(cosh(ν+ik) − 1))` | matches pin's integrand `exp(2τ(cosh(ν+ik)−1))` exactly | exact (no constant lost) |
| normalisation of the inversion | `(2π)^{-1} ∫_{-π}^{π} e^{ik(m−n)} dk = 1_{m=n}` | pin has `((2π:ℝ):ℂ)⁻¹` and `exp(-(k n) I)`: signs and `2π` agree with orthogonality, so `(2π)^{-1}∫ e^{-ikn} Σ_m h_τ(m)e^{(ν+ik)m} dk = e^{νn} h_τ(n)` | exact; the pin has the correct sign and normalisation (no counterexample) |
| torus MGF | `z = e^{2πik/L}`: `Σ_m h_τ(m) e^{2πikm/L} = exp(-2τ(1 − cos(2πk/L)))` | equals the summand factor in `hkT` | exact |
| finite orthogonality | `L^{-1} Σ_{k ∈ ℤ_L} e^{2πik(m−x)/L} = 1_{m ≡ x (mod L)}` | gives `Σ_{y} h_τ(x.val + Ly) = L^{-1} Σ_k e^{-2πik x.val/L} e^{-2τ(1-cos(2πk/L))}`; the sum is real because `g(k) = e^{-2τ(1−cos(2πk/L))}` is invariant under `k ↦ -k`, so the `sin` part cancels and `e^{-iθ}` may be replaced by `cos θ` as in `hkT` | exact; `m ↦ (x.val, y)` with `m = x.val + L y` is a bijection `ℤ ≅ [0,L) × ℤ`, `x.val ∈ [0,L)` |
| `TorusMass` | `Σ_x hkT = Σ_x Σ_y h_τ(x.val + Ly) = Σ_{m∈ℤ} h_τ(m) = 1` | non-negativity of `hkT` follows from `Images` (`HasSum` of non-negative terms, `τ ≥ 0`) | exact; includes `L = 1` (`ZMod 1`, `x.val = 0`, `hkT = 1`) |
| cosh bound (Chernoff, not a B1 target) | `cosh ν ≤ e^{ν²/2}` | used only by B2; B1 needs no `c₀` | not a B1 constant |
| Hypotheses of the pins | `τ ≥ 0` in `Nonneg, Mass, MGF, Tilt, Images, TorusMass`; none in `Symm`; `ν ∈ ℝ`, `n ∈ ℤ`, `L ≥ 1` (`NeZero L`) | `Symm` holds for all `τ` since the tsum is termwise symmetric | all pins consistent as written |

### (ii) One concrete nondegenerate instance

Hypotheses of the ticket's four instances: `hkZ_mass` at `τ = 1` (`0 ≤ 1`); `hkZ_tilt` at `τ = 1, ν = 1/2, n = 3`; `hkT_mass` at `L = 5, τ = 1`; `hkT_hasSum_images` at `L = 5, τ = 1, x = 2`. All have `τ = 1 > 0`, `L = 5 ≥ 3`, `ZMod 5` nonempty and non-collapsed, `ν = 1/2 ≠ 0`, `n = 3`, `x = 2 ≠ 0`. There are no external hypotheses (only Mathlib and the pinned definitions).

Command (pure Python 3.9, no scipy/mpmath; the script is in the session scratchpad and contains no Lean):

`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2009_pf.py`

Output (verbatim):

```
N_j(n)=C(j,(j+n)/2) [|n|<=j, j=n mod 2], symmetric, <=2^j; brute force j<=10, |n|<=12: OK
  t=0.1 n=5 series=6.834135661823e-08 e^-2t I_n=6.834135661823e-08
  t=1 n=5 series=1.329761094188e-03 e^-2t I_n=1.329761094188e-03
  t=10 n=20 series=6.572504291369e-06 e^-2t I_n=6.572504291369e-06
max rel err series vs e^{-2t}I_n(2t) (I_n from its power series): 0.000e+00
Tilt, 36-case grid tau{.1,1,10} nu{0,.5,1} n{0,1,5,20}: max |int-lhs|/e^{2t(cosh nu-1)} = 1.10e-15 ; max |Im int|/same = 6.88e-17 ; max rel err where lhs/scale>1e-6: 3.80e-12
tau=0.1: mass-1=-2.22e-16 ; |MGF(z=.7+.4i)-exp(t(z+1/z)-2t)|=3.33e-16 ; majorant<=2e^{2t(cosh nu-1)} ok for nu=.5,1
tau=1: mass-1=0.00e+00 ; |MGF(z=.7+.4i)-exp(t(z+1/z)-2t)|=1.14e-16 ; majorant<=2e^{2t(cosh nu-1)} ok for nu=.5,1
tau=10: mass-1=-1.11e-16 ; |MGF(z=.7+.4i)-exp(t(z+1/z)-2t)|=3.30e-16 ; majorant<=2e^{2t(cosh nu-1)} ok for nu=.5,1
hkT vs sum_y h(x+Ly): max rel err 1.20e-12 (L{3,4,7}, tau{.1,1,10}, all x); max|sum_x hkT-1| 1.33e-15; min hkT 1.402e-04
instance hkZ_mass tau=1: sum_n h = 1.000000000000000
instance Tilt tau=1 nu=1/2 n=3: e^{nu n}h = 1.290333078249865e-01 ; integral = 1.290333078249870e-01 -9.5e-18 i
instance hkT_mass L=5 tau=1: sum_x hkT = 1.000000000000000 ; min_x hkT = 1.2206e-01
instance Images L=5 tau=1 x=2: hkT = 1.220644065765342e-01 ; sum_y h(2+5y) = 1.220644065765342e-01
```

Reading of the output: (1) `walkCount` formula, symmetry and the `2^j` bound verified by brute force. (2) `hkZ` from the series equals `e^{-2τ} I_n(2τ)` (with `I_n` its power series `Σ_m (x/2)^{2m+n}/(m!(m+n)!)`) at `τ ∈ {0.1, 1, 10}`, `n ∈ {0,1,5,20}`, to floating-point equality; this checks the combinatorics `Σ_j τ^j N_j(n)/j! = Σ_m τ^{2m+n}/(m!(m+n)!)`. (3) `Tilt`: the integral (trapezoid rule on a periodic integrand, 4096 points) equals `e^{νn}h_τ(n)` over the 36 combinations `τ ∈ {.1,1,10}`, `ν ∈ {0,.5,1}`, `n ∈ {0,1,5,20}`; error is measured against the scale `e^{2τ(cosh ν − 1)}` because for tiny `h_τ(n)` the absolute rounding error `~1e-16` of the quadrature dominates; the imaginary part is `~1e-17`. (4) `Mass`, `MGF` at `z = 0.7+0.4i` and the majorant bound hold numerically (sums truncated at `|n| ≤ 120`). (5) `Images` and `TorusMass`: `hkT` equals the image sum `Σ_{|y| ≤ 40} h_τ(x+Ly)` at `L ∈ {3,4,7}`, `τ ∈ {.1,1,10}`, all `x`; `Σ_x hkT = 1`, `min hkT > 0`. (6) the four compiled instances of the ticket have the listed values: mass `1`, tilt `0.12903330782499` on both sides, `hkT_mass` at `L=5` sums to `1`, `hkT(5,1,2) = 0.12206440657653` equals its image sum.

Verdicts (mathematics only):
- `hkZ_nonneg`: PASS. Every term `τ^j N_j(n)/j!` is `≥ 0` for `τ ≥ 0`.
- `hkZ_mass`: PASS. Summability from the double-series bound; `∑' = 1` from `MGF` at `z = 1`.
- `hkZ_neg`: PASS. `N_j(-n) = N_j(n)` termwise (`ε ↦ -ε` bijection), valid for all real `τ`.
- `hkZ_hasSum_mgf`: PASS. Absolute convergence of the double series for all `z ≠ 0`, `Σ_n N_j(n)z^n = (z+z^{-1})^j` (binomial theorem), Fubini over `ℤ × ℕ`, exponential series.
- `hkZ_tilt`: PASS. MGF at `z = e^{ν+ik}`, orthogonality, exchange of `∑'` and `∫` by the majorant `h_τ(m)e^{|ν||m|}` (summable, `≤ 2e^{2τ(cosh ν−1)}`, constant in `k` on a finite-measure interval). Pin sign and normalisation confirmed; no contour shift and no `poissonMeasure` needed.
- `hkT_hasSum_images`: PASS. MGF at `z = e^{2πik/L}`, finite orthogonality, reindexing `ℤ ≅ [0,L) × ℤ`, realness by `k ↦ -k` symmetry.
- `hkT_mass`: PASS. From `Images` and `Mass` (nonnegativity of each `hkT` as a `HasSum` limit of nonnegative terms).
- No pin is false or unprovable as written; no BLOCKED input.

Overall verdict: PASS.

## (a′) Preflight corrections — Sat Oct  3 00:37:14 UTC 2026

Row `N_j(n) ≤ 2^j` of table (i) calls absolute convergence of the series for every real τ "needed for `Symm`". It is not: `Symm` holds termwise (`walkCount j (-n) = walkCount j n`) and `hkZ_neg` is proved with no summability. Absolute convergence is true and is used for `MGF` and `Mass` (τ ≥ 0). No verdict changes.

## (b) Script output — stage 1b (`prover-max`)

Commands run in the worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2009` unless stated. Scratch scripts are in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad`.

Commit, diff against `main`, build, hygiene:
```
$ git log --format="%h %ad %s" --date=iso main..t/T2009; git diff --stat main...t/T2009; git status --short
c9fd239 2026-10-02 17:32:45 -0700 T2009: correct the RBM2D line citation in the sum_exp_orth docstring
99d4f47 2026-10-02 17:31:00 -0700 T2009: PT-B1 heat kernel on Z and Z_L (route H pilot, part 1)
 RBM3D/Propagator/HeatKernel1D.lean | 582 +++++++++++++++++++++++++++++++++++++
 1 file changed, 582 insertions(+)
```
Build log of the module after its last edit (tool log, 00:32:16 UTC; the file is unchanged since, `git status --short` is empty above):
```
✔ [3361/3361] Built RBM3D.Propagator.HeatKernel1D (5.1s)
Build completed successfully (3361 jobs).
```
```
$ lake build RBM3D.Propagator.HeatKernel1D 2>&1 | tail -3   # re-run now, up to date
Build completed successfully (3361 jobs).
```
```
$ lake env lean axioms.lean   # import RBM3D.Propagator.HeatKernel1D; #print axioms RBM.Heat.<each public name>
'RBM.Heat.walkCount' [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ' [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkT' [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ_nonneg' [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ_mass' [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ_neg' [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ_hasSum_mgf' [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ_tilt' [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkT_hasSum_images' [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkT_mass' [propext, Classical.choice, Quot.sound]
```
```
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Propagator/HeatKernel1D.lean; echo exit=$?
exit=1
```
Name-clash grep of every new public name and of the namespace, over `RBM3D`, `RBM3D.lean`, `blueprint/src` (new file excluded):
```
$ grep -rnwE "walkCount|hkZ|hkT|hkZ_[a-zA-Z_]+|hkT_[a-zA-Z_]+|RBM[.]Heat" RBM3D RBM3D.lean blueprint/src --exclude=HeatKernel1D.lean; echo exit=$?
exit=1
```
Target statements and compiled instances, extracted from the file by script (`[n]` = line in the file):
```
$ python3 statements.py   # regex over RBM3D/Propagator/HeatKernel1D.lean
[139] theorem hkZ_nonneg : ∀ τ : ℝ, 0 ≤ τ → ∀ n : ℤ, 0 ≤ hkZ τ n
[145] theorem hkZ_neg : ∀ τ : ℝ, ∀ n : ℤ, hkZ τ (-n) = hkZ τ n
[150] theorem hkZ_hasSum_mgf : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℂ, z ≠ 0 →
    HasSum (fun n : ℤ => (hkZ τ n : ℂ) * z ^ n)
      (Complex.exp ((τ : ℂ) * (z + z⁻¹) - 2 * (τ : ℂ)))
[221] theorem hkZ_mass : ∀ τ : ℝ, 0 ≤ τ → Summable (hkZ τ) ∧ ∑' n : ℤ, hkZ τ n = 1
[233] theorem hkZ_tilt : ∀ τ : ℝ, 0 ≤ τ → ∀ ν : ℝ, ∀ n : ℤ,
    ((Real.exp (ν * n) * hkZ τ n : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi,
        Complex.exp (-((k : ℂ) * (n : ℂ)) * Complex.I)
          * Complex.exp (2 * (τ : ℂ) * (Complex.cosh ((ν : ℂ) + (k : ℂ) * Complex.I) - 1))
[444] theorem hkT_hasSum_images : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 ≤ τ → ∀ x : ZMod L,
    HasSum (fun y : ℤ => hkZ τ ((x.val : ℤ) + (L : ℤ) * y)) (hkT L τ x)
[529] theorem hkT_mass : ∀ (L : ℕ) [NeZero L], ∀ τ : ℝ, 0 ≤ τ →
    (∀ x : ZMod L, 0 ≤ hkT L τ x) ∧ ∑ x : ZMod L, hkT L τ x = 1
-- instances --
[552] example : 0 ≤ hkZ 1 2 := hkZ_nonneg 1 zero_le_one 2
[555] example : Summable (hkZ 1) ∧ ∑' n : ℤ, hkZ 1 n = 1 := hkZ_mass 1 zero_le_one
[558] example : hkZ 1 (-3) = hkZ 1 3 := hkZ_neg 1 3
[561] example : HasSum (fun n : ℤ => (hkZ 1 n : ℂ) * (2 : ℂ) ^ n)
    (Complex.exp (((1 : ℝ) : ℂ) * ((2 : ℂ) + (2 : ℂ)⁻¹) - 2 * ((1 : ℝ) : ℂ))) :=
  hkZ_hasSum_mgf 1 zero_le_one 2 two_ne_zero
[566] example : ((Real.exp ((1 / 2 : ℝ) * ((3 : ℤ) : ℝ)) * hkZ 1 3 : ℝ) : ℂ) =
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi,
      Complex.exp (-((k : ℂ) * ((3 : ℤ) : ℂ)) * Complex.I)
        * Complex.exp (2 * ((1 : ℝ) : ℂ) *
          (Complex.cosh (((1 / 2 : ℝ) : ℂ) + (k : ℂ) * Complex.I) - 1)) :=
  hkZ_tilt 1 zero_le_one (1 / 2) 3
[574] example : HasSum (fun y : ℤ => hkZ 1 (((2 : ZMod 5).val : ℤ) + ((5 : ℕ) : ℤ) * y))
    (hkT 5 1 2) :=
  hkT_hasSum_images 5 1 zero_le_one 2
[579] example : (∀ x : ZMod 5, 0 ≤ hkT 5 1 x) ∧ ∑ x : ZMod 5, hkT 5 1 x = 1 :=
  hkT_mass 5 1 zero_le_one
```
Statements against the pins (`docs/tickets/checks/T2009-check.lean`): text identity of the three definitions and seven theorem types (whitespace-normalised), then a Lean-level check (the pins copied into `namespace RBM.Heat`, then `example : Pin := theorem`, 7 examples):
```
$ python3 pin_cmp.py && lake env lean pinconf2.lean; echo "lean exit=$?"
def walkCount:  IDENTICAL
def hkZ      :  IDENTICAL
def hkT      :  IDENTICAL
Nonneg    -> hkZ_nonneg        : IDENTICAL
Mass      -> hkZ_mass          : IDENTICAL
Symm      -> hkZ_neg           : IDENTICAL
MGF       -> hkZ_hasSum_mgf    : IDENTICAL
Tilt      -> hkZ_tilt          : IDENTICAL
Images    -> hkT_hasSum_images : IDENTICAL
TorusMass -> hkT_mass          : IDENTICAL
lean exit=0
```
Merge-time axiom audit emulated (scratch file: `import RBM3D`, `import RBM3D.Propagator.HeatKernel1D`, `#assert_rbm_axioms`; the hub runs the real `lake build`):
```
$ lake env lean merge_emul.lean 2>&1 | head -3; echo exit=${pipestatus[1]}
axiom audit: 518 theorems, 176 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit=0
```
Port (CLAUDE.md §5.2): RBM2D `RBM2D/Propagator/Symbol.lean:144-149` at `c9a24cf` (`inv_mul_sum_stdAddChar`); only the last two proof steps are reused, in `sum_exp_orth` here:
```
$ git -C ../RBM2D --no-optional-locks log -1 --format="%h %ad %s" c9a24cf; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Propagator/Symbol.lean
c9a24cf Fri Oct 2 09:03:18 2026 -0700 T2273: merge dead-code closure tool and report
 RBM2D/Propagator/Symbol.lean | 15 +--------------
 1 file changed, 1 insertion(+), 14 deletions(-)
```
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Propagator/Symbol.lean | grep -n "sum_mulShift\|split_ifs <;> simp \[hL\]"; awk 'NR>=361 && NR<=376 && /sum_mulShift|split_ifs <;> simp$/ {print NR": "$0}' RBM3D/Propagator/HeatKernel1D.lean
147:  rw [AddChar.sum_mulShift u (ZMod.isPrimitive_stdAddChar L), ZMod.card]
149:  split_ifs <;> simp [hL]
375:   rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar L), ZMod.card]
376:   split_ifs <;> simp
```

Narrative (facts of this run only):
1. All seven targets are proved in `RBM3D/Propagator/HeatKernel1D.lean` (branch `t/T2009`). The module builds with no warning; every public declaration uses only the three standard axioms; the diff against `main` is the sole writable file.
2. Pins: the three definitions and the seven theorem types are text-identical to the check file, and each theorem is accepted at the pin copied from the check file (Lean-level, exit 0). No pin was changed, no hypothesis added, no target weakened.
3. Route (no contour shift, no `poissonMeasure`). `walkCount_hasSum` (generic `Field`) gives `Σ_n N_j(n) z^n = (z+z⁻¹)^j` on a finite support. `hkZ_hasSum_mgf` sums `a_j(n) z^n` over `ℕ × ℤ`: `summable_prod_of_nonneg` with the exponential series gives absolute summability, then `HasSum.prod_fiberwise` over `j` and, through `Equiv.prodComm`, over `n`. `hkZ_mass` is the case `z = 1`.
4. `hkZ_tilt`: the MGF at `z = exp(ν + ik)` gives the integrand as `Σ_m G_m(k)`; `MeasureTheory.hasSum_integral_of_summable_integral_norm` on `Ioc (-π) π` (summable norms `2π h_τ(m) e^{mν}` from the MGF at `z = e^ν`); `∫ G_m` is `0` for `m ≠ n` by `integral_exp_mul_complex` and `exp(2πi (m - n)) = 1`, and `2π h_τ(n) e^{nν}` for `m = n`.
5. `hkT_hasSum_images`: the indicator of `m ≡ x (mod L)` as a finite Fourier sum (`sum_exp_orth`); the MGF at `z_k = exp(2πi k.val/L)` has value `exp(-2τ(1 - cos θ))` (`mgf_unit_circle`); restriction of the `ℤ`-sum to the progression `y ↦ x.val + L y` by `Function.Injective.hasSum_iff`; the real part of the complex sum is `hkT`, so no `k ↦ -k` symmetry argument is needed.
6. `hkT_mass`: non-negativity from `hkT_hasSum_images` and `hkZ_nonneg`; `Σ_x hkT = 1` by finite orthogonality in the position variable (`sum_cos_orth`) and `g(0) = 1`. This differs from the route `Images` + `Mass` suggested in the ticket (it avoids the reindexing `ℤ ≃ ZMod L × ℤ`); the theorem is the pin.
7. `hkZ_neg` is termwise (bijection `ε ↦ !ε`, `walkCount_neg`); see (a′).
8. Instances: seven `example`s in the file at `τ = 1`, `ν = 1/2`, `n = 3`, `L = 5`, `x = 2`: the four of the ticket and one each for `hkZ_nonneg`, `hkZ_neg`, `hkZ_hasSum_mgf`. Hypotheses `0 ≤ 1` and `2 ≠ 0` are discharged; no external hypothesis exists.

## (c) Verified Mathlib names (all 48 present in the environment; `names2.lean` output: `names used: 48; missing: []`)

- `hasSum_sum_of_ne_finset_zero`: `(∀ b ∉ s, f b = 0) → HasSum f (∑ b ∈ s, f b)` (the expected `HasSum` type must be given by ascription, else `SummationFilter.LeAtTop ?m` is stuck)
- `Finset.sum_fiberwise_of_maps_to`: `(∀ i ∈ s, g i ∈ t) → ∑ j ∈ t, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i`
- `Fintype.sum_pow`: `(∑ a, f a) ^ n = ∑ p : Fin n → ι, ∏ i, f (p i)` (give `f` explicitly)
- `summable_prod_of_nonneg`: `0 ≤ f → (Summable f ↔ (∀ x, Summable fun y => f (x, y)) ∧ Summable fun x => ∑' y, f (x, y))`
- `HasSum.prod_fiberwise`: `HasSum f a → (∀ b, HasSum (fun c => f (b, c)) (g b)) → HasSum g a`
- `Summable.prod_factor`: `Summable f → ∀ b, Summable fun c => f (b, c)`
- `Equiv.hasSum_iff`, `Equiv.summable_iff`, `Equiv.prodComm`: transport along `ℤ × ℕ ≃ ℕ × ℤ`
- `Summable.of_norm`; `Real.summable_pow_div_factorial`: `Summable fun n => x ^ n / ↑n.factorial`
- `NormedSpace.expSeries_div_hasSum_exp`: `HasSum (fun n => x ^ n / ↑n.factorial) (NormedSpace.exp x)`; `Complex.exp_eq_exp_ℂ`: `Complex.exp = NormedSpace.exp`
- `Complex.hasSum_ofReal`, `Complex.summable_ofReal`, `Complex.ofReal_tsum`, `Complex.hasSum_re`, `Complex.re_sum`, `Complex.re_ofReal_mul`: real/complex transfer
- `MeasureTheory.hasSum_integral_of_summable_integral_norm`: `(∀ i, Integrable (F i) μ) → (Summable fun i => ∫ a, ‖F i a‖ ∂μ) → HasSum (fun i => ∫ a, F i a ∂μ) (∫ a, ∑' i, F i a ∂μ)`
- `Continuous.integrableOn_Ioc`: used as `(hG_cont m).integrableOn_Ioc` for `Integrable (G m) (volume.restrict (Set.Ioc a b))`
- `intervalIntegral.integral_of_le`: `a ≤ b → ∫ x in a..b, f x ∂μ = ∫ x in Set.Ioc a b, f x ∂μ`
- `intervalIntegral.integral_const_mul`: `∫ x in a..b, r * f x ∂μ = r * ∫ x in a..b, f x ∂μ`
- `MeasureTheory.integral_const`, `MeasureTheory.Measure.restrict_apply_univ`, `Real.volume_Ioc`: volume of `Ioc (-π) π`
- `integral_exp_mul_complex`: `c ≠ 0 → ∫ x in a..b, Complex.exp (c * ↑x) = (Complex.exp (c * ↑b) - Complex.exp (c * ↑a)) / c`
- `Complex.exp_int_mul`: `Complex.exp (↑n * z) = Complex.exp z ^ n`; `Complex.exp_int_mul_two_pi_mul_I`: `Complex.exp (↑n * (2 * ↑π * I)) = 1`
- `Complex.two_cosh`: `2 * cosh x = exp x + exp (-x)`; `Complex.two_cos`: `2 * cos x = exp (x * I) + exp (-x * I)`
- `Complex.exp_ofReal_mul_I_re`: `(exp (↑x * I)).re = Real.cos x`; `Complex.norm_exp`: `‖exp z‖ = Real.exp z.re`; `Complex.ofReal_cos`, `Complex.ofReal_exp`
- `ZMod.stdAddChar_coe`: `stdAddChar ↑j = exp (2 * π * I * j / N)`; `ZMod.isPrimitive_stdAddChar`; `AddChar.sum_mulShift`: `∑ x, ψ (x * b) = ↑(if b = 0 then Fintype.card R else 0)`
- `ZMod.card`, `ZMod.natCast_zmod_val` (`↑a.val = a`), `ZMod.natCast_self` (`↑n = 0`), `ZMod.intCast_zmod_eq_zero_iff_dvd` (`↑a = 0 ↔ ↑b ∣ a`)
- `Function.Injective.hasSum_iff`: `Injective g → (∀ x ∉ Set.range g, f x = 0) → (HasSum (f ∘ g) a ↔ HasSum f a)`
- `hasSum_ite_eq`: `HasSum (fun b' => if b' = b then a else 0) a`; `hasSum_sum`: finite sum of `HasSum`s; `HasSum.nonneg`: `(∀ i, 0 ≤ g i) → HasSum g a → 0 ≤ a`
- `Finset.card_nbij'`, `zpow_add₀`
- Verified absent (script: `names claimed absent: 3; actually present: []`): `Complex.cosh_eq` (`Trigonometric.lean:761` has `cosh_eq (x : ℝ)`; use `Complex.two_cosh`), `zpow_sum` (private `zpow_sum_aux` by induction with `zpow_add₀`), `Real.exp_int_mul` (use `Complex.exp_int_mul` and casts).

## (d) Open issues and paper-delta candidates

- No blocking issue: all seven targets delivered, no pin changed.
- Paper-delta candidates: none (`T2009a` not used). Route H is an internal proof (DECISIONS §4 "证法不同") and no Lean/paper statement differs in this file.
- For PT-B2: `Summable (fun m : ℤ => hkZ τ m * Real.exp (m * ν))` is a local `have` inside `hkZ_tilt`, not an exported lemma; PT-B2 obtains it from `hkZ_hasSum_mgf` at `z = Complex.exp ν`. If the ticket wants an exported name, it must say so.
- The import `Mathlib.Analysis.SpecialFunctions.Trigonometric.Series` is present as the ticket requires and is unused in this file (stated in the module docstring).
