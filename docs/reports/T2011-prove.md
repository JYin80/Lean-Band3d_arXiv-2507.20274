Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 01:25:06 UTC 2026

Notation: `w = ν + ik`, `F(k) = exp(2τ(cosh w − 1))`, `m(n) = min(n²/τ, |n|)`, `A = 2τ cosh ν`, `B = 4τ/π²`.
Common facts (all `n ≥ 0`, `ν = min(n/(4τ), 1)`): `|F| = e^{2τ(cosh ν−1)} e^{−A(1−cos k)}` (since `Re cosh w = cosh ν cos k`);
`e^{νn}h(n±1)` from `hkZ_tilt` at the same `ν` gives `e^{νn}D1(n) = (2π)⁻¹∫e^{−ikn}(e^{−w}−1)F dk`,
`e^{νn}D2(n) = (2π)⁻¹∫e^{−ikn}(e^{w}+e^{−w}−2)F dk`, `D1(n) = h(n+1)−h(n)`, `D2(n) = h(n+1)+h(n−1)−2h(n)`.
Every bound is `|target| ≤ e^{−νn+2τ(cosh ν−1)} · (2π)⁻¹∫_{−π}^{π} (factor)·e^{−A(1−cos k)} dk`.

### (i) Exponent table

| Item | Value | Constraint / derivation | Slack |
|---|---|---|---|
| `ν` | `min(n/(4τ), 1)` | `ν ∈ [0,1]` so `cosh ν−1 ≤ K ν²` is available | none needed |
| `K` (Chernoff) | `cosh1−1 = 0.5431` (ratio `(cosh ν−1)/ν²` increasing); alt. `e^{1/2}/2 = 0.8244` via `Real.cosh_le_exp_half_sq` and `e^x−1 ≤ xe^x` | `cosh ν−1 ≤ Kν²`, `ν ≤ 1` | alt. route is weaker but sufficient |
| Branch `n ≤ 4τ` (`ν = n/4τ`) | `−νn+2τ(cosh ν−1) ≤ −(1/4 − K/8) n²/τ` = `−0.1821 n²/τ` (K=0.5431), `−0.1470 n²/τ` (K=0.8244) | `≤ −c₀ n²/τ ≤ −c₀ m(n)` since `m ≤ n²/τ` | `0.1821−0.18 = 0.0021`; `0.147−0.14 = 0.007` |
| Branch `n > 4τ` (`ν=1`, `τ < n/4`) | `−n+2τ(cosh1−1) ≤ −(1−K/2) n` = `−0.7285 n` (K=0.5431), `−0.5878 n` (K=0.8244) | `≤ −c₀ n ≤ −c₀ m(n)` since `m ≤ |n|` | `0.5485` (resp. `0.4478`) |
| `c₀` | `0.18` (cosh1 route) or `0.14` (Mathlib `cosh_le_exp_half_sq` route); this table uses `c₀ = 0.14` below | binding constraint is branch 1: `1/4−K/8 ≥ c₀` | as above |
| Jordan | `1−cos k = 2sin²(k/2) ≥ (2/π²)k²` on `[−π,π]` (`sin x ≥ 2x/π`, `0≤x≤π/2`, `x=|k|/2`) | `A(1−cos k) ≥ 2τ·(2/π²)k² = B k²`, using `A ≥ 2τ`, `1−cos ≥ 0` | exact |
| Gaussian, moments `M_j := (2π)⁻¹∫_ℝ |k|^j e^{−Bk²}dk` | `M₀ = (√π/4)τ^{−1/2} = 0.4431τ^{−1/2}`; `M₁ = (π/8)τ⁻¹ = 0.3927τ⁻¹`; `M₂ = (π^{5/2}/32)τ^{−3/2} = 0.5467τ^{−3/2}` | from `∫e^{−Bk²}=√(π/B)`, `∫|k|e^{−Bk²}=1/B`, `∫k²e^{−Bk²}=√π/(2B^{3/2})`; truncation `[−π,π]⊂ℝ` only decreases (nonneg. integrand) | numeric agreement to 6 digits (script) |
| Target (a), `n ≥ 0` | `h ≤ e^{−c₀m}·min(1, (√π/4)τ^{−1/2})`: `C=1`, `c = c₀` | `min(1,·)`: `(2π)⁻¹∫e^{−A(1−cos k)} ≤ 1` (trivial) and `≤ M₀` | script max ratio `0.9980` (`C=1`, `c=0.14` and `0.18`) |
| (a), `n < 0` | `hkZ_neg`: `h(n) = h(−n)`, exponent symmetric | exact, no shift | none |
| |`e^{−w}−1`| | `≤ |k| + ν` (triangle: `e^{−ν}|e^{−ik}−1| + (1−e^{−ν})`); also `≤ 2` | ticket's "`ν·e`" is not needed: the factor is `1` | sharper than ticket |
| |`e^{w}+e^{−w}−2`| | `|2(cosh w −1)| ≤ 2(cosh ν−1) + 2(1−cos k) + 2 sinh ν|sin k| ≤ 1.0862ν² + k² + 2.3504ν|k| ≤ 2.2614ν² + 2.1752k²`; also `≤ 2cosh1+2 = 5.086` | uses `cosh ν cos k −1 = (cosh ν−1)cos k −(1−cos k)`, `sinh ν ≤ ν sinh1`, `2ν|k| ≤ ν²+k²` | script check of coefficients |
| Absorption 1 (for D1) | `ν√τ ≤ min(s/4, √τ)`, `s = n/√τ`; `≤ 1.6210·e^{(c₀/2)m}` | `sup_x x e^{−(c₀/2)x²}`-type: `1/√(c₀e) = 1.6210` (branch `n ≤ τ`: `s/4`, sup `0.4053`; branch `n > τ`: `√τ e^{−c₀τ/2} ≤ 1.6210`, uses `m = n ≥ τ`) | exact sup values |
| Absorption 2 (for D2) | `(ν√τ)² ≤ 5.2554·e^{(c₀/2)m}` | branch `n ≤ τ`: `(s²/16)e^{−c₀s²/2} ≤ 1/(8c₀e) = 0.3285`; branch `n > τ`: `τe^{−c₀τ/2} ≤ 2/(c₀e) = 5.2554` | exact |
| Target (b), `τ ≥ 1`, `n ≥ 0` | `|D1| ≤ e^{−c₀m}(νM₀+M₁) ≤ (0.4431·1.6210+0.3927)τ⁻¹e^{−(c₀/2)m} = 1.1110τ⁻¹e^{−0.07m}` | `ν M₀ = 0.4431 (ν√τ)/τ` | — |
| (b), `τ < 1`, `n ≥ 0` | `|D1| ≤ 2e^{−c₀m}` (`|e^{−w}−1| ≤ 2`, `|F| ≤ e^{2τ(cosh ν−1)}`) | `min(1,τ⁻¹)=1` | — |
| (b), `n < 0` | `D1(n) = −D1(−n−1)`; `g(x)=min(x²/τ,x)` is 2-Lipschitz on `x ≥ 0` (slope `2x/τ ≤ 2` for `x ≤ τ`, `1` after), so `m(−n−1) ≥ m(n) − 2`: factor `e^{2c}`, `c = 0.07` → `1.1503` | `C₁ = max(1.1110, 2)·1.1503 = 2.3005 ≤ 2.31` | `c = 0.07` |
| **(b) result** | `C₁ = 2.31`, `c₁ = 0.07` | | script max ratio `0.4629` |
| Target (c), `τ ≥ 1`, `n ≥ 0` | `|D2| ≤ e^{−c₀m}(2.2614ν²M₀ + 2.1752M₂) ≤ (2.2614·0.4431·5.2554 + 2.1752·0.5467)τ^{−3/2}e^{−0.07m} = 6.4553τ^{−3/2}e^{−0.07m}` | `ν²M₀ = 0.4431(ν√τ)²τ^{−3/2}` | — |
| (c), `τ < 1` | `|D2| ≤ 5.0862e^{−c₀m}` (`2cosh1+2`) | `min(1,τ^{−3/2}) = 1` | `5.0862 < 6.4553` |
| (c), `n < 0` | `D2(−n) = D2(n)` exactly (since `h(−j) = h(j)`): no shift | | — |
| **(c) result** | `C₂ = 6.46`, `c₂ = 0.07` | | script max ratio `0.3087` |

Pins close with: (a) `C=1, c=0.14` (or `0.18`); (b) `C=2.31, c=0.07`; (c) `C=6.46, c=0.07`. The dispatcher's pair `C=1, c=0.09` for (b), (c) fails on the script grid (ratios `1.0909`, `1.9940` at `τ=10⁻³`; the dispatcher's own check reported 1.094, 1.999); the proof above does not use it. Pins have unspecified `C, c`, so `C₁=2.31, c₁=0.07` is all the existential needs.
No contour shift, `poissonMeasure` or Bessel function is used; the only tilt input is `hkZ_tilt` (merged) at `ν ≥ 0`.

### (ii) Concrete nondegenerate instance and numeric check

Instance for the three `example`s: `τ = 100`, `n = 0` (`ν = 0`, `m = 0`, `τ ≥ 1` branch; `hkZ 100 0 = 0.028227 ≤ C·(1/10)`, `|D1| = 7.066e-5 ≤ C₁/100`, `|D2| = 1.413e-4 ≤ C₂/1000`). All hypotheses are `0 < τ` and `n ∈ ℤ`; no external hypothesis is introduced (DECISIONS §16), so no limit computation is needed.
`hkZ` is computed from the definition (series `e^{−2τ}Σ_j τ^j N_j(n)/j!`, `N_j(n) = C(j,(j+n)/2)` for parity-matching `j`) and independently from `(2π)⁻¹∫e^{−ikn}e^{2τ(cos k −1)}dk` (`= e^{−2τ}I_n(2τ)`; `scipy` is not installed, so `ive` was not used) on the grid `τ ∈ {10⁻³, 0.1, 1, 10, 10³, 10⁴}`, `n ∈ {0, ±1, ±2, ±5, ±20, ±100, ±1000}` (and `n±1` for differences).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/pf.py` (run from `/Users/junyin/Lean_proof/RBM3D`). Output, verbatim:
```
cosh1-1=0.5431  cosh(nu)-1<=(cosh1-1)nu^2 ; via exp(nu^2/2)-1<=nu^2/2*e^{1/2}: coeff=0.8244
 cosh1        branch n<=4tau: exponent -(1/4-K/8) n^2/tau = -0.1821 ; branch n>4tau (nu=1): -(1-K/2) n = -0.7285
 exp_half_sq  branch n<=4tau: exponent -(1/4-K/8) n^2/tau = -0.1470 ; branch n>4tau (nu=1): -(1-K/2) n = -0.5878
Jordan 1-cos k >= 0.2026 k^2 ; B=4tau/pi^2 ; M0=sqrt(pi)/4=0.4431 M1=pi/8=0.3927 M2=pi^(5/2)/32=0.5467 (times tau^{-(j+1)/2})
 moment j=0 closed=0.443113 numeric=0.443113
 moment j=1 closed=0.392699 numeric=0.392699
 moment j=2 closed=0.546669 numeric=0.546669
absorb: nu*sqrt(tau)<=1.6210 e^{(c0/2)m} (branch n<=tau: 0.4053); (nu sqrt tau)^2<=5.2554 e^{(c0/2)m} (branch n<=tau: 0.3285)
D1: tau>=1 C=1.1110 ; tau<1 C=2.0000 (|e^{-w}-1|<=2) ; n<0 shift factor e^{2c}=1.1503 -> C1=2.3005
D2: tau>=1 C=6.4553 ; tau<1 C=5.0862 (|e^w+e^-w-2|<=2cosh1+2) -> C2=6.4553 (no shift, D2 even)
check |2(cosh w-1)|<=2.2614 nu^2+2.1752 k^2: coeffs 2.2614 2.1752
max |series - (2pi)^-1 int e^{-ikn}e^{2tau(cos k-1)}| over grid (cannot use scipy ive: not installed): 4.96e-14
max ratio a c=.14                      = 0.9980 at (tau,n)=(0.001, 0)
max ratio a c=.18                      = 0.9980 at (tau,n)=(0.001, 0)
max ratio D1 C=2.31 c=.07              = 0.4629 at (tau,n)=(0.001, -1)
max ratio D2 C=6.46 c=.07              = 0.3087 at (tau,n)=(0.001, 0)
max ratio D1 C=1 c=.09 (dispatcher)    = 1.0909 at (tau,n)=(0.001, -1)
max ratio D2 C=1 c=.09 (dispatcher)    = 1.9940 at (tau,n)=(0.001, 0)
tilt-stage bounds (pre-absorption, Gaussian-moment form) max ratio over grid, n>=0 (valid for all tau): 0.6962
instance tau=100,n=0: h=0.028227 <= 1*(1/10): True ; |D1|=7.066e-05 <= 2.31/100: True ; |D2|=1.413e-04 <= 6.46/1000: True
```

### Verdict per target

- Target 1 \`hkZ_le\` (Bound): PASS (\`C=1, c=0.14\`; closes with slack \`0.007\` in the Chernoff exponent).
- Target 2 \`hkZ_diff1_le\` (Diff1): PASS (\`C=2.31, c=0.07\`).
- Target 3 \`hkZ_diff2_le\` (Diff2): PASS (\`C=6.46, c=0.07\`).

## (a′) Preflight corrections

None: section (a) was not edited and no statement in it changes a verdict. The constants proved below differ from those of (a) (see the narrative); the pins leave `C, c` free.

## (b) Script output — Sat Oct  3 01:52:40 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2011`, branch `t/T2011`; `$F` = `RBM3D/Propagator/HeatBounds1D.lean`, `$MAIN` = `/Users/junyin/Lean_proof/RBM3D`, `$SP` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2011` (scratch scripts and scratch Lean files, outside the repository). Output of `$SP/evidence.sh`, verbatim:
```
$ date -u
Sat Oct  3 01:51:13 UTC 2026
$ git log --oneline -1; git diff --stat main...t/T2011; git status --short | wc -l
92a174c T2011: heat kernel bounds on Z (hkZ_le, hkZ_diff1_le, hkZ_diff2_le)
 RBM3D/Propagator/HeatBounds1D.lean | 871 +++++++++++++++++++++++++++++++++++++
 1 file changed, 871 insertions(+)
       0
$ lake build RBM3D.Propagator.HeatBounds1D 2>&1 | tail -5
Build completed successfully (3387 jobs).
$ lake build 2>&1 | tail -1    # whole library, root #assert_rbm_axioms
Build completed successfully (3691 jobs).
$ lake env lean $SP/RootAudit.lean 2>&1 | head -1    # import RBM3D + HeatBounds1D, #assert_rbm_axioms
axiom audit: 734 theorems, 286 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean $SP/RootBase.lean 2>&1 | head -1     # import RBM3D only
axiom audit: 731 theorems, 286 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -nE "sorry|admit|native_decide|^axiom|^ *axiom " $F; echo "grep exit=$?"
grep exit=1
$ grep -nE "^(noncomputable )?(theorem|lemma|def|abbrev|instance|structure|class|inductive)" $F | grep -v private
635:theorem hkZ_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
670:theorem hkZ_diff1_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
734:theorem hkZ_diff2_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
$ grep -rnE "hkZ_le|hkZ_diff1_le|hkZ_diff2_le" RBM3D --include="*.lean" | grep -v "^$F"; echo "grep exit=$?"
grep exit=1
$ (cd $MAIN && grep -rnE "hkZ_le|hkZ_diff1_le|hkZ_diff2_le" RBM3D docs/tickets/checks --include="*.lean"; echo "grep exit=$?")
grep exit=1
$ python3 $SP/pins.py
Bound  vs hkZ_le        identical after whitespace normalisation: True
Diff1  vs hkZ_diff1_le  identical after whitespace normalisation: True
Diff2  vs hkZ_diff2_le  identical after whitespace normalisation: True
ALL IDENTICAL
$ lake env lean $SP/PinCheck.lean; echo "exit=$?"
'RBM.Heat.hkZ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ_diff1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ_diff2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -n "^example : \(Bound\|Diff1\|Diff2\)" $SP/PinCheck.lean
27:example : Bound := RBM.Heat.hkZ_le
29:example : Diff1 := RBM.Heat.hkZ_diff1_le
31:example : Diff2 := RBM.Heat.hkZ_diff2_le
$ grep -n "refine ⟨max" $F
637:  refine ⟨max 1 ((2 * Real.pi)⁻¹ * (1 * (2 * Real.sqrt (2 * Real.pi)))), 1 / 8,
673:  refine ⟨max (3 * (Real.pi + 1)) (9 * ((2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi)))), 1 / 16,
737:  refine ⟨max (27 * (Real.pi + 1) ^ 2) (648 * ((2 * Real.pi)⁻¹ * (2 * Real.sqrt (2 * Real.pi)))),
$ python3 $SP/numcheck.py | head -6
hkZ_le       C=1.0000 c=0.1250
hkZ_diff1_le C=12.4248 c=0.0625
hkZ_diff2_le C=517.0292 c=0.0625
max ratio (value / bound) hkZ_le        = 0.9980 at (tau,n)=(0.001, 0)
max ratio (value / bound) hkZ_diff1_le  = 0.0854 at (tau,n)=(0.001, -1)
max ratio (value / bound) hkZ_diff2_le  = 0.0039 at (tau,n)=(0.001, 0)
$ (cd .lake/packages/mathlib && grep -rn "cos_quadratic_upper_bound" Mathlib; echo "grep exit=$?")
grep exit=1
$ (cd .lake/packages/mathlib && grep -rln "theorem one_le_cosh\|theorem exp_one_lt_three\|lemma cosh_le_exp_half_sq\|lemma cos_le_one_sub_mul_cos_sq" Mathlib)
Mathlib/Analysis/Complex/ExponentialBounds.lean
Mathlib/Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean
Mathlib/Analysis/SpecialFunctions/Trigonometric/Series.lean
Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean
```
`pins.py` regex-extracts the bodies of `def Bound/Diff1/Diff2` from `docs/tickets/checks/T2011-check.lean` and the type of each theorem from `$F`, collapses whitespace and compares. `PinCheck.lean` is the check file's `namespace RBM.Heat.T2011Check` block with `import RBM3D.Propagator.HeatBounds1D`, followed by `open RBM.Heat.T2011Check in example : Bound := RBM.Heat.hkZ_le` (and `Diff1`, `Diff2`; lines 27, 29, 31 above) and `#print axioms` of the three theorems.

Target statements, extracted from `$F` by script (from `theorem hkZ…` to `:= by`):
```lean
theorem hkZ_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
    hkZ τ n ≤ C * min 1 (τ ^ (-(1 / 2 : ℝ))) * Real.exp (-c * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)|) := by
theorem hkZ_diff1_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
    |hkZ τ (n + 1) - hkZ τ n|
      ≤ C * min 1 τ⁻¹ * Real.exp (-c * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)|) := by
theorem hkZ_diff2_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
    |hkZ τ (n + 1) + hkZ τ (n - 1) - 2 * hkZ τ n|
      ≤ C * min 1 (τ ^ (-(3 / 2 : ℝ))) * Real.exp (-c * min ((n : ℝ) ^ 2 / τ) |(n : ℝ)|) := by
```
Compiled nonempty instances (`$F`, section `Compiled instances`; `τ = 100`): the three required ones at `n = 0` in full, then the statements of the three at `n = 7`, where `exp (-c · 49/100)` is nontrivial (all six compile in the build above):
```lean
-- `hkZ_le` at `τ = 100`, `n = 0`: `h_100(0) ≤ C / 10`.
example : ∃ C : ℝ, hkZ 100 0 ≤ C * (1 / 10) := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_le
  refine ⟨C, ?_⟩
  have h0 := h 100 (by norm_num) 0
  rw [rpow_hundred_neg_half] at h0
  norm_num at h0
  linarith

-- `hkZ_diff1_le` at `τ = 100`, `n = 0`: `|h_100(1) - h_100(0)| ≤ C / 100`.
example : ∃ C : ℝ, |hkZ 100 1 - hkZ 100 0| ≤ C / 100 := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_diff1_le
  refine ⟨C, ?_⟩
  have h0 := h 100 (by norm_num) 0
  norm_num at h0
  linarith

-- `hkZ_diff2_le` at `τ = 100`, `n = 0`: `|h_100(1) + h_100(-1) - 2 h_100(0)| ≤ C / 1000`.
example : ∃ C : ℝ, |hkZ 100 1 + hkZ 100 (-1) - 2 * hkZ 100 0| ≤ C / 1000 := by
  obtain ⟨C, c, hC, hc, h⟩ := hkZ_diff2_le
  refine ⟨C, ?_⟩
  have h0 := h 100 (by norm_num) 0
  rw [rpow_hundred_neg_three_halves] at h0
  norm_num at h0
  linarith

-- `hkZ_le` at `τ = 100`, `n = 7`: the exponential factor `exp (-c · 49/100)` is nontrivial.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    hkZ 100 7 ≤ C * (1 / 10) * Real.exp (-(c * (49 / 100))) := by
-- `hkZ_diff1_le` at `τ = 100`, `n = 7`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |hkZ 100 8 - hkZ 100 7| ≤ C / 100 * Real.exp (-(c * (49 / 100))) := by
-- `hkZ_diff2_le` at `τ = 100`, `n = 7`.
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |hkZ 100 8 + hkZ 100 6 - 2 * hkZ 100 7| ≤ C / 1000 * Real.exp (-(c * (49 / 100))) := by
```

### Narrative
- All three pins are proved as theorems, types identical to the pin bodies (text diff and `example : Bound := hkZ_le` etc. above); no hypothesis was added; the only merged theorem used is `hkZ_tilt` (besides the definition `hkZ`): `grep -n "hkZ_nonneg\|hkZ_mass\|hkZ_neg\|hkZ_hasSum_mgf\|hkZ_tilt\|hkT" $F` hits two comment lines (20, 124) and one use (line 161) in the tool log; all helpers are `private` (only the three theorems are public); `$F` is the only file changed (871 lines); nothing was ported from RBM1D/RBM2D (neither was read).
- Tool log: `lake build RBM3D.Propagator.HeatBounds1D` at 01:44:05 UTC printed `✔ [3387/3387] Built RBM3D.Propagator.HeatBounds1D (5.6s)` and `Build completed successfully (3387 jobs).`, no warnings; the committed file is that file. The root `RBM3D.lean` (hub-owned) does not yet import the module, so the full `lake build` above does not compile it; the merged state is emulated by `#assert_rbm_axioms` in a scratch file importing `RBM3D` and the module: 731 → 734 theorems (the three targets), 286 definitions, 0 axioms, only `propext`/`Classical.choice`/`Quot.sound`.
- Route (as in (a); no contour shift, Poisson measure or Bessel function). `tilt_combo`: from `hkZ_tilt` at `n-1, n, n+1`, `e^{νn}(α h(n+1) + β h(n) + γ h(n-1)) = (2π)⁻¹ ∫_{-π}^{π} e^{-ikn}(α e^{-w} + β + γ e^{w}) F dk`, `w = ν + ik`. `tilt_combo_bound`: `|·| ≤ e^{-νn + 2τ(cosh ν - 1)} (2π)⁻¹ ∫ g(k) e^{-(τ/4)k²} dk` when the symbol is `≤ g(k)`, using `‖F‖ = e^{2τ(cosh ν cos k - 1)} ≤ e^{2τ(cosh ν - 1)} e^{-(τ/4)k²}` (Jordan `1 - cos k ≥ k²/8`: `Real.cos_le_one_sub_mul_cos_sq`, `π ≤ 4`).
- Symbols: `h`: `1`; `h(n+1) - h(n)`: `e^{-w} - 1`, `‖·‖ ≤ 3(|k| + |ν|)`; second difference: `e^{w} + e^{-w} - 2 = e^{w}(e^{-w} - 1)²`, `‖·‖ ≤ 27(|k| + |ν|)²` (`|ν| ≤ 1`, `Real.exp_one_lt_three`).
- Each target is proved twice and merged by `min_combine`: (T) trivial, the symbol is bounded and `(2π)⁻¹ ∫_{-π}^{π} ≤ K`; (G) Gaussian, with `s = √τ` (substituted once per theorem; `(s²)^{-1/2} = s⁻¹`, `(s²)^{-3/2} = (s³)⁻¹`), the pointwise bounds `|k| e^{-s²k²/8} ≤ 2/s`, `k² e^{-s²k²/8} ≤ 8/s²` and `integral_gaussian` at `b = s²/8` give `∫ ≤ K 2√(2π)/s`.
- Deviations from the route sketched in (a), all inside the free `C, c` of the pins: (i) one signed tilt `ν = ± min(|n|/(4τ), 1)` for every `n ∈ ℤ`, so the reduction to `n ≥ 0` and the lemma `m(-n-1) ≥ m(n) - 2` of (a) are not needed; (ii) Chernoff step with `cosh u - 1 ≤ u²` on `[0, 1]` (`Real.cosh_le_exp_half_sq`, `Real.exp_bound_div_one_sub_of_interval`), so `-νn + 2τ(cosh ν - 1) ≤ -(1/8) min(n²/τ, |n|)`: `c = 1/8` instead of (a)'s 0.14/0.18; (iii) absorption by the single inequality `τν² ≤ m/4` (`m = min(n²/τ, |n|)`, lemma `tau_mul_sq_le`), which gives `|ν|√τ ≤ e^{m/16}`, `(|ν|√τ)² ≤ 4 e^{m/16}` and `c = 1/16` for (b), (c) instead of (a)'s 0.07; (iv) the `C` of (b), (c) are 12.42 and 517.03 instead of 2.31 and 6.46.
- Sanity (not part of the proof): the explicit constants satisfy the bounds on the grid of (a) (plus `τ = 100`, `n = 7`): sup ratios 0.9980, 0.0854, 0.0039.

## (c) Verified Mathlib names — Sat Oct  3 01:52:40 UTC 2026

`#check @name` for each name below in `$SP/names.lean` (imports the new module), `lake env lean` exit 0, 31 results, 0 stderr lines (`python3 $SP/names.py`; signatures abbreviated):
```
integral_gaussian : ∀ (b : ℝ), ∫ (x : ℝ), Real.exp (-b * x ^ 2) = √(Real.pi / b)
@integrable_exp_neg_mul_sq : ∀ {b : ℝ}, 0 < b → MeasureTheory.Integrable (fun x => Real.exp (-b * x ^ 2)…
@MeasureTheory.setIntegral_le_integral : ∀ {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X} [inst …
@intervalIntegral.integral_mono_on : ∀ {f g : ℝ → ℝ} {a b : ℝ} {μ : MeasureTheory.Measure ℝ}, a ≤ b → In…
@intervalIntegral.norm_integral_le_integral_norm : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_…
@intervalIntegral.integral_const_mul : ∀ {𝕜 : Type u_1} {a b : ℝ} {μ : MeasureTheory.Measure ℝ} [inst : …
@intervalIntegral.integral_add : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ …
@intervalIntegral.integral_const : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace …
@intervalIntegral.integral_of_le : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace …
Real.cosh_le_exp_half_sq : ∀ (x : ℝ), Real.cosh x ≤ Real.exp (x ^ 2 / 2)
@Real.cos_le_one_sub_mul_cos_sq : ∀ {x : ℝ}, |x| ≤ Real.pi → Real.cos x ≤ 1 - 2 / Real.pi ^ 2 * x ^ 2
Real.pi_le_four : Real.pi ≤ 4
Real.one_le_cosh : ∀ (x : ℝ), 1 ≤ Real.cosh x
@Real.exp_bound_div_one_sub_of_interval : ∀ {x : ℝ}, 0 ≤ x → x < 1 → Real.exp x ≤ 1 / (1 - x)
Real.add_one_le_exp : ∀ (x : ℝ), x + 1 ≤ Real.exp x
Real.exp_one_lt_three : Real.exp 1 < 3
@Real.norm_exp_I_mul_ofReal_sub_one_le : ∀ {x : ℝ}, ‖Complex.exp (Complex.I * ↑x) - 1‖ ≤ ‖x‖
@Complex.norm_exp_sub_one_le : ∀ {x : ℂ}, ‖x‖ ≤ 1 → ‖Complex.exp x - 1‖ ≤ 2 * ‖x‖
Complex.norm_exp : ∀ (z : ℂ), ‖Complex.exp z‖ = Real.exp z.re
Complex.cosh_add : ∀ (x y : ℂ), Complex.cosh (x + y) = Complex.cosh x * Complex.cosh y + Complex.sinh x …
Complex.cosh_mul_I : ∀ (x : ℂ), Complex.cosh (x * Complex.I) = Complex.cos x
Complex.sinh_mul_I : ∀ (x : ℂ), Complex.sinh (x * Complex.I) = Complex.sin x * Complex.I
@Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.sqrt_eq_rpow : ∀ (x : ℝ), √x = x ^ (1 / 2)
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
@Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
@Real.sq_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x ^ 2 = x
@Real.sqrt_sq : ∀ {x : ℝ}, 0 ≤ x → √(x ^ 2) = x
Real.cosh_neg : ∀ (x : ℝ), Real.cosh (-x) = Real.cosh x
@Real.exp_le_one_iff : ∀ {x : ℝ}, Real.exp x ≤ 1 ↔ x ≤ 0
@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosM…
exit=0, 31 #check results, 0 lines of stderr
```
Import facts (from the `grep -rln` above): `Real.one_le_cosh` is in `Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp`, `Real.exp_one_lt_three` in `Mathlib.Analysis.Complex.ExponentialBounds` (the file imports both; `Real.exp_one_lt_d9` and `Real.one_le_cosh` were unknown constants before those imports were added). Verified absent: `Real.cos_quadratic_upper_bound` (`grep` exit 1 above; the Jordan bound is `Real.cos_le_one_sub_mul_cos_sq`). `Real.mul_le_sin` (named in the ticket) exists in `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean:83` and is not used.

## (d) Open issues and paper-delta candidates

- Paper-delta candidates: none (`T2011a` is not needed): the targets are route-H lemmas (S3-Z of the T2003 design), not statements of the paper.
- Route H go/no-go (DECISIONS §14), part B2: all three pins were provable as written; no pin was changed, weakened or given a new hypothesis.
- Explicit constants are not exported as lemmas (not required): `(C, c) = (1, 1/8)`, `(12.42, 1/16)`, `(517.03, 1/16)`, read off the `refine ⟨max …⟩` lines above. Fable's `c₀ = 0.18 / 0.14` is not reproduced (`1/8` here). The dispatcher's pair `C = 1, c = 0.09` for (b), (c) is not claimed: (a) (lines 37, 63-64) reports it fails at `τ = 10⁻³`. Downstream tickets must take `c` from the `∃` of the pins or ask for an amend with a primed explicit lemma.
- The Gaussian-majorant lemmas (`tilt_combo_bound`, `gauss_bound`, `trivial_bound`, `min_combine`) are `private`; a downstream file that needs them (for example the torus-images ticket) must copy them or request an export by amend.
