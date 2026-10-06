Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 10:47 UTC 2026

Notation: `N = L^d`, `v_i = BAspec d L g i` (real), `w_i(μ) = v_i - E - μ`, `F_E(μ) = μ - N⁻¹ Σ_i w_i(μ)⁻¹`, `A = 1 - N⁻¹ Σ_i w_i(m)⁻²`.
There are no exponents or thresholds in T2285 (the pin is qualitative, ticket "Not targets"); the constants are the following.

### (i) Exponent table

| # | Quantity | Value / form | Constraint it must satisfy | Slack |
|---|---|---|---|---|
| 1 | Reality of the shifted argument (M0) | `Im(E + iη + m) = η + Im m` | `≠ 0` so that `BAMB_trace_eq_sum` applies | `≥ Im m > 0` for `η ≥ 0` (clause 1, `BASelf` gives `Im m > 0`) |
| 2 | M0 equivalence | `BASelf d L g (E+iη) m ↔ 0 < Im m ∧ F_E(m+iη) = iη` | `F_E` has `μ - iη = N⁻¹ Σ w_i⁻¹` as `m = N⁻¹ tr M`, `μ = m + iη`, `E + iη + m = E + μ` | identity, none |
| 3 | Strict derivative (M1) | `F_E'(μ) = 1 - N⁻¹ Σ w_i(μ)⁻²` (`d/dμ w⁻¹ = w⁻²` since `dw/dμ = -1`), `Im μ ≠ 0` | each `w_i(μ) ≠ 0`: `Im w_i = -Im μ` | at `μ = m`: `Im m > 0` |
| 4 | Stability gap `A ≠ 0` (clause 1) | `Re A ≥ 2 (Im m)²` (`BAgapReal_holds`, uses `3 ≤ L`, `0 < g`) | `A ≠ 0` for IFT (`HasStrictDerivAt.localInverse` needs `f' ≠ 0`) | `Re A - 2(Im m)² = 1.35946` at the instance below; `Re A > 0` strictly, since `Im m > 0` |
| 5 | IFT branch | `G = localInverse F_E A m`, `F_E(G(y)) = y` for `y` near `F_E(m) = 0`, `G(0) = m`, `G` continuous at `0` | `F_E(m) = 0` is `BASelf` at `η = 0` (M0 with `η = 0`) | local radius not needed (only `y = iη → 0`, `η ∈ 𝓝[>] 0`) |
| 6 | Branch identification | `m_η = G(iη) - iη → m`, `Im m_η > 0` eventually, `BASelf (E+iη) m_η`, so `BAm = m_η` | uniqueness `BASelf_unique` at `Im z = η ≥ 0` (no `L`, `g` hypothesis); existence at `η > 0` | none: `Im m_η → Im m > 0` |
| 7 | Predicted slope | `dm_η/dη|_{0} = i(1/A - 1)`; `|1/A - 1| = 0.49703` at the instance | consistency of the IFT branch with the numerics | script (ii): `|m_η - m0|/η = 0.49703` for `η = 10⁻⁶, 10⁻⁸` |
| 8 | Closedness (M3) | `zₖ → z`, `mₖ → m`, `Im zₖ ≥ 0`, `Im m > 0` | `Im(z + m) ≥ Im m > 0` so `(v_i - (z+m))⁻¹` is continuous at the limit | `Im(z+m) ≥ Im m` (`Im z = lim Im zₖ ≥ 0`) |
| 9 | Resolvent bound (M4) | `‖m‖ ≤ 1/Im m` for a solution with `Im z ≥ 0` | `‖(v_i - (z+m))⁻¹‖ ≤ 1/|Im(z+m)| ≤ 1/Im m` | `0.56068 ≤ 1.78355` at the instance; `|m| ≤ 1/ε` on a contradicting sequence `Im m_k ≥ ε` |
| 10 | Clause 2 contradiction | `ε ≤ Im m_k`, `m_k → m*` along a subsequence, `Im m* ≥ ε > 0`, `zₖ = E + iηₖ → E` | M3 gives `BASelf d L g E m*`, against `¬ ∃ m, BASelf d L g E m` | none: strict contradiction; lower side `Im BAm ≥ 0` by `BAm_im_nonneg` |
| 11 | `ρ_N` form (target 5) | `ρ_N(E) = BArho = (BAm d L g E).im / π` | with a solution `BAm(E) = m` (`BAm_real_eq_of_self`) and clause 1; without, `BAm(E) = 0` (the `dite` default) and clause 2 | none |
| 12 | Hypotheses actually used | clause 1: `3 ≤ L`, `0 < g` (via the gap only); clause 2 and `BASelf_of_tendsto`: neither; no `3 ≤ d`; `NeZero L` only | `BASelf_exists`, `BASelf_unique`, `BAm_im_nonneg` are unconditional (merged statements, `MFixedPoint.lean:691,715`, `CouplingWindow.lean:320`) | targets 2 and 4 carry fewer hypotheses than 3 and 5: consistent with the check file |
| 13 | Gap instance threshold | no solution when `2 + 2 d |g| < |E|` (`baSelf_none_of_gt`, `FlowPins.lean:785`) | `(d, g, E) = (3, 10, 63)`: `2 + 2·3·10 = 62 < 63` | `63 - 62 = 1` |

Route of (M2): IFT (`HasStrictDerivAt.localInverse`); the contraction fallback is not needed by the mathematics above.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `L = 4` (`N = 64`, `Ψ^{(B)}` the nearest-neighbour adjacency, `Adj := zdistD = 1`, `Lattice.lean:108`), spectrum `{0, ±2, ±4, ±6}`.
- Clause 1 / targets 2, 3, 5: `(g, E, m) = (g0P, EP, m0P)`, the merged flow point of `CouplingWindowInst` (`flowP_data.2.2 : BASelf 3 4 g0P EP m0P`, `g0P_pos`), recomputed from `w = 6i/5` at `(L, g) = (4, 10)`: `m_S = N⁻¹ Σ (10 λ_i - w)⁻¹`, `z_S = w - m_S`, `t₀ = Im m_S/(Im m_S + Im z_S)`, `g0P = √t₀·10`, `m0P = m_S/√t₀`, `EP = (t₀ Re z_S - (1-t₀) Re m_S)/√t₀` (`MFixedPoint.lean:279-280`, `CouplingWindow.lean:861-864`). Hypotheses: `3 ≤ 4`, `0 < g0P`, `BASelf` (residual below), `NeZero 4`.
- Clause 2 / targets 4, 5, 6: `(g, E) = (10, 63)`, hypothesis `¬ ∃ m, BASelf 3 4 10 63` by `2 + 2·3·10 = 62 < 63`.
- Target 2 (`BASelf_of_tendsto`): constant sequences `zs ≡ EP`, `ms ≡ m0P`, `Im EP = 0 ≥ 0`, `Im m0P > 0`.
- Target 6 (`baMBoundary_holds 3`): both clauses at `d = 3`, `L = 4`.

Command (Python 3, mpmath, 40 digits; scratch script outside the repository, mathematics only): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2285/pre.py`
The script builds `Ψ^{(B)}` from the `Adj` definition, computes the eigenvalues, the flow point, `A`, the Newton IFT branch `m_η` at `F_E(μ) = iη`, and the gap instance by fixed-point iteration plus `findroot`.

Output (verbatim, exit 0):
```
N = 64 distinct lam: [np.float64(-6.0), np.float64(-4.0), np.float64(-2.0), np.float64(-0.0), np.float64(2.0), np.float64(4.0), np.float64(6.0)]
t0P = 0.21830732  g0P = 4.6723369  EP = 2.8792e-43  m0P = (-2.8791728e-43 + 0.56068043j)
hyp BASelf: Im m0P > 0: True  residual |m - N^-1 tr M| = 1.15e-41  (3<=L: True  0<g0P: True )
A = (1.9881897 - 3.9849425e-45j)  Re A = 1.9881897  2(Im m0)^2 = 0.62872508  slack Re A - 2(Im m)^2 = 1.35946
predicted dm/deta = i(1/A-1): (-1.00811e-45 - 0.49703j)  modulus 0.49703
norm bound |m0| = 0.56068  <= 1/Im m0 = 1.78355
eta=0.01  m_eta=(-2.242077543e-44 + 0.5557326847j)  |m_eta-m0|/eta=0.494774  Im>0:True  resid=1.15e-41
eta=0.0001  m_eta=(-5.605193857e-44 + 0.5606307252j)  |m_eta-m0|/eta=0.497007  Im>0:True  resid=2.06e-84
eta=1.0e-6  m_eta=(-1.121038771e-43 + 0.5606799289j)  |m_eta-m0|/eta=0.49703  Im>0:True  resid=2.06e-84
eta=1.0e-8  m_eta=(7.8472714e-44 + 0.560680421j)  |m_eta-m0|/eta=0.49703  Im>0:True  resid=3.09e-84
gap instance: 2+2*d*|g| = 62  < E = 63.0 : True
max |v_i - E| min over i (>= 63-60 = 3): 3.0
eta=2.0  Im m=0.00328209  Im m/eta=0.00164104  resid=5.2e-43  |m|<=1/Im m: True
eta=0.1  Im m=0.000219375  Im m/eta=0.00219375  resid=4.9e-43  |m|<=1/Im m: True
eta=0.01  Im m=2.19574e-5  Im m/eta=0.00219574  resid=2.28e-42  |m|<=1/Im m: True
eta=0.001  Im m=2.19576e-6  Im m/eta=0.00219576  resid=1.8e-42  |m|<=1/Im m: True
eta=0.0001  Im m=2.19576e-7  Im m/eta=0.00219576  resid=1.89e-42  |m|<=1/Im m: True
eta=1.0e-6  Im m=2.19576e-9  Im m/eta=0.00219576  resid=1.42e-42  |m|<=1/Im m: True
eta=1.0e-8  Im m=2.19576e-11  Im m/eta=0.00219576  resid=1.39e-42  |m|<=1/Im m: True
rho(10,63) = 0 (no root with Im m>0 since |E|>62)
```
Reading of the output:
- `EP ≈ 3·10⁻⁴³` is the numerical zero of `EP` (the spectrum is symmetric); the residual `1.15·10⁻⁴¹` of `(self_m)` at `(g0P, EP, m0P)` is working precision, `Im m0P = 0.56068 > 0`, `3 ≤ L`, `0 < g0P = 4.67234`: every hypothesis of targets 2, 3, 5 holds.
- Stability gap: `Re A = 1.98819 ≥ 2 (Im m0P)² = 0.628725` (row 4).
- Clause 1: `|m_η - m0P|/η → 0.49703 = |1/A - 1|` as `η → 0⁺` (row 7); every `m_η` solves `(self_m)` at `E + iη` with `Im m_η > 0` (residual `≤ 1.15·10⁻⁴¹`), so by `BASelf_unique` it is `BAm(E + iη)`.
- Clause 2 at `(10, 63)`: `Im m(63 + iη)/η` is constant `0.0021958` for `η ≤ 10⁻²`, so `Im m(63 + iη) → 0`; `|m| ≤ 1/Im m` holds on every row (row 9); `min_i |v_i - E| = 3` (distance from `63` to `60`, the top atom `10·6`). `ρ_N(63) = 0` at `g = 10` (row 13), so target 5 at `(4, 10, 63)` reads `Tendsto (Im m/π) → 0 = BArho`.
- External hypotheses: none (every hypothesis is a merged data predicate `BASelf` or an order relation).

### Verdicts
- Target 1 (private `Boundary_*` lemmas: M0, M1, gap `≠ 0`, `‖m‖ ≤ 1/Im m`): PASS (rows 2-4, 9).
- Target 2 `BASelf_of_tendsto`: PASS (row 8; instance: constant sequences at `(EP, m0P)`).
- Target 3 `BAm_tendsto_of_self`: PASS (rows 1-7; instance `(4, g0P, EP, m0P)`, all hypotheses hold).
- Target 4 `BAm_im_tendsto_zero`: PASS (rows 9, 10, 12; instance `(4, 10, 63)`, hypothesis holds by row 13).
- Target 5 `BArho_tendsto`: PASS (row 11; instances at both points).
- Target 6 `baMBoundary_holds`: PASS (targets 3 and 4 together, `NeZero L` from `3 ≤ L`).
- No FAIL or BLOCKED: every hypothesis set is satisfiable at the instance, no exponent to close, no missing input.

## (a′) Preflight corrections
None.

## (b) Script output — Tue Oct  6 10:57:08 UTC 2026

### Commit, build, full build
```
$ git log -1 --format="%h %an <%ae>" ; git diff --stat main...t/T2285 ; wc -l RBM3D/BA/Boundary.lean
06e86c6 Jun Yin <321276894+JYin80@users.noreply.github.com>
 RBM3D/BA/Boundary.lean | 349 +++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 349 insertions(+)
     349 RBM3D/BA/Boundary.lean
$ lake build RBM3D.BA.Boundary > build.txt 2>&1 ; tail -2 build.txt ; echo exit $?
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3739 jobs).
exit 0
$ lake build 2>&1 | tail -1   (worktree; RBM3D.lean does not import Boundary until the hub merge)
Build completed successfully (4089 jobs).
exit 0
$ grep -nE "sorry|admit|native_decide|axiom" RBM3D/BA/Boundary.lean ; echo exit $?
exit 1
```

### Axioms of the five public theorems
```
$ lake env lean scratch/axioms.lean   (import RBM3D.BA.Boundary; #print axioms for each)
'RBM.BA.BASelf_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_tendsto_of_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BArho_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMBoundary_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Target statements, extracted from the file by script
```
$ python3 extract: from each "theorem <name>" line to the first line ending in ":= by"
RBM3D/BA/Boundary.lean:164
theorem BASelf_of_tendsto (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (zs ms : ℕ → ℂ)
    (hz : Tendsto zs atTop (𝓝 z)) (hm : Tendsto ms atTop (𝓝 m)) (hzs : ∀ k, 0 ≤ (zs k).im)
    (hself : ∀ k, BASelf d L g (zs k) (ms k)) (hmim : 0 < m.im) : BASelf d L g z m := by

RBM3D/BA/Boundary.lean:190
theorem BAm_tendsto_of_self (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (E : ℝ) (m : ℂ)
    (hm : BASelf d L g (E : ℂ) m) :
    Tendsto (fun η : ℝ => BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m) := by

RBM3D/BA/Boundary.lean:244
theorem BAm_im_tendsto_zero (d L : ℕ) [NeZero L] (g E : ℝ) (hnone : ¬ ∃ m : ℂ, BASelf d L g (E : ℂ) m) :
    Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0) := by

RBM3D/BA/Boundary.lean:282
theorem BArho_tendsto (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (E : ℝ) :
    Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) (𝓝[>] (0 : ℝ))
      (𝓝 (BArho d L g E)) := by

RBM3D/BA/Boundary.lean:305
theorem baMBoundary_holds (d : ℕ) : BAmBoundary d := by

```

### Private helpers and public declarations (grep)
```
$ grep -nE "^(private )?(theorem|def|lemma)" RBM3D/BA/Boundary.lean | cut -c1-100
54:private def Boundary_F (d L : ℕ) [NeZero L] (g E : ℝ) (μ : ℂ) : ℂ :=
58:private theorem Boundary_self_iff (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) :
68:private theorem Boundary_self_iff_F (d L : ℕ) [NeZero L] (g E η : ℝ) (hη : 0 ≤ η) (m : ℂ) :
85:private theorem Boundary_F_hasStrictDerivAt (d L : ℕ) [NeZero L] (g E : ℝ) (μ : ℂ) (hμ : μ.im ≠ 0
111:private theorem Boundary_gap_ne_zero (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (E :
124:private theorem Boundary_norm_le_inv_im (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im)
155:private theorem Boundary_BAm_of_none (d L : ℕ) [NeZero L] (g : ℝ) (z : ℂ) (h : ¬ ∃ m : ℂ, BASelf
164:theorem BASelf_of_tendsto (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (zs ms : ℕ → ℂ)
190:theorem BAm_tendsto_of_self (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (E : ℝ) (m : 
244:theorem BAm_im_tendsto_zero (d L : ℕ) [NeZero L] (g E : ℝ) (hnone : ¬ ∃ m : ℂ, BASelf d L g (E :
282:theorem BArho_tendsto (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (E : ℝ) :
305:theorem baMBoundary_holds (d : ℕ) : BAmBoundary d := by
325:private theorem Boundary_none_10_63 : ¬ ∃ m : ℂ, BASelf 3 4 10 ((63 : ℝ) : ℂ) m := by
```

### Check-file equality (acceptance): scratch = check imports + import RBM3D.BA.Boundary + rest of the check file + 5 examples
```
$ tail -9 scratch/check_eq.lean ; lake env lean scratch/check_eq.lean > out ; echo exit $?   (output = the #check lines of the check file)
noncomputable section
namespace RBM.BA.T2285Check
example : BASelf_of_tendsto_pin := @RBM.BA.BASelf_of_tendsto
example : BAm_tendsto_of_self_pin := @RBM.BA.BAm_tendsto_of_self
example : BAm_im_tendsto_zero_pin := @RBM.BA.BAm_im_tendsto_zero
example : BArho_tendsto_pin := @RBM.BA.BArho_tendsto
example : baMBoundary_holds_pin := @RBM.BA.baMBoundary_holds
end RBM.BA.T2285Check
end
exit 0 ; lines of output:       80 ; lines containing 'error': 0
```

### Registry pre-check (acceptance): scratch = import RBM3D, import RBM3D.BA.Boundary, #assert_rbm_axioms
```
$ lake env lean scratch/precheck.lean ; echo exit $?   (compared with the same without the Boundary import)
exit 0
exit (without Boundary) 0
axiom audit: 8190 theorems, 2656 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ diff pre_base.txt pre_with.txt
1c1
< axiom audit: 8185 theorems, 2656 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 8190 theorems, 2656 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -c "BASelf\|BAm\b\|Boundary" pre_with.txt   (flagged premises mentioning the new vocabulary)
0
```

### Name-clash grep (worktree base b39ac53 plus the new file; Probe/ excluded; T2283.md)
```
$ grep -rnE "BASelf_of_tendsto|BAm_tendsto_of_self|BAm_im_tendsto_zero|BArho_tendsto|baMBoundary_holds|BoundaryInst|Boundary_" RBM3D --include=*.lean | grep -v Probe/ | grep -v "^RBM3D/BA/Boundary.lean" | wc -l
       0
$ grep -cE <same pattern> /Users/junyin/Lean_proof/RBM3D/docs/tickets/T2283.md
0
```

### The compiled instances (RBM3D/BA/Boundary.lean, namespace RBM.BA.BoundaryInst), extracted by sed
```
$ sed -n "/^namespace BoundaryInst/,/^end BoundaryInst/p" RBM3D/BA/Boundary.lean | grep -v "^$"
namespace BoundaryInst
open RBM.BA.CouplingWindowInst
/-- (I1) the pin at `d = 3`. -/
example : BAmBoundary 3 := baMBoundary_holds 3
/-- (I2) clause 1 at the merged flow point `(g, E, m) = (g0P, EP, m0P)` (`flowP_data.2.2`, `g0P_pos`). -/
example : Tendsto (fun η : ℝ => BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m0P) :=
  BAm_tendsto_of_self 3 4 (by norm_num) g0P g0P_pos EP m0P flowP_data.2.2
/-- The gap point `(g, E) = (10, 63)`: `2 + 2·3·|10| = 62 < 63`, so `(self_m)` has no solution. -/
private theorem Boundary_none_10_63 : ¬ ∃ m : ℂ, BASelf 3 4 10 ((63 : ℝ) : ℂ) m := by
  rintro ⟨m, hm⟩
  exact baSelf_none_of_gt 3 4 10 63 (by norm_num) m hm
/-- (I3) clause 2 at the gap point `(g, E) = (10, 63)`. -/
example : Tendsto (fun η : ℝ => (BAm 3 4 10 (((63 : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  BAm_im_tendsto_zero 3 4 10 63 Boundary_none_10_63
/-- (I4) `ρ_N(E) = π⁻¹ Im m(E + i0)` at the flow point and at the gap point. -/
example : Tendsto (fun η : ℝ => (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) (𝓝[>] (0 : ℝ))
    (𝓝 (BArho 3 4 g0P EP)) :=
  BArho_tendsto 3 4 (by norm_num) g0P g0P_pos EP
example : Tendsto (fun η : ℝ => (BAm 3 4 10 (((63 : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) (𝓝[>] (0 : ℝ))
    (𝓝 (BArho 3 4 10 63)) :=
  BArho_tendsto 3 4 (by norm_num) 10 (by norm_num) 63
/-- (I5) closedness along the constant sequences at `(EP, m0P)`. -/
example : BASelf 3 4 g0P (EP : ℂ) m0P :=
  BASelf_of_tendsto 3 4 g0P (EP : ℂ) m0P (fun _ => (EP : ℂ)) (fun _ => m0P) tendsto_const_nhds tendsto_const_nhds
    (fun _ => by simp) (fun _ => flowP_data.2.2) flowP_data.2.2.1
end BoundaryInst
```

### Ports
```
No statement or proof was copied from RBM1D or RBM2D (RBM2D FreeConvStability not applicable, ticket Role); no git command was run in them.
One proof body is copied inside RBM3D: `Boundary_norm_le_inv_im` from `BAself_im_le_one` (RBM3D/BA/CouplingWindow.lean:335-360 (`hv`, `hnorm`), last commit e1fec21).
$ git log -1 --format=%h -- RBM3D/BA/CouplingWindow.lean
e1fec21
```

### Narrative (stage 1b)
- Route of (M2): the inverse function theorem (`HasStrictDerivAt.localInverse` for `Boundary_F` at the real-axis solution `m`, `Boundary_F_hasStrictDerivAt`, `Boundary_gap_ne_zero`); the contraction fallback of the ticket was not used (`BAm_tendsto_of_self`, `RBM3D/BA/Boundary.lean:190`).
- Clause 2 (`BAm_im_tendsto_zero`, `:244`): `Filter.frequently_iff_seq_forall` gives a sequence `η_k ↓ 0` with `Im m(E + iη_k) ≥ ε`; `Boundary_norm_le_inv_im` bounds `‖m_k‖ ≤ 1/ε`; `tendsto_subseq_of_bounded` gives a limit; `BASelf_of_tendsto` makes it a real-axis solution, against the hypothesis.
- Hypotheses actually used (read off the signatures above): `BASelf_of_tendsto` and `BAm_im_tendsto_zero` carry neither `3 ≤ L` nor `0 < g`; `BAm_tendsto_of_self` and `BArho_tendsto` carry both, used only through `BAgapReal_holds`; no theorem carries `3 ≤ d`; every statement is for every `d`.
- Statements equal section 2 of the check file (the compiled equality above, exit 0, 0 error lines); `BAmBoundary` is unchanged (`baMBoundary_holds` proves the merged pin).
- Imports are exactly the eight listed in the ticket (Targets); the check file's two extra Mathlib imports (`Deriv.Basic`, `Bounded`) are not imported directly and the build passes.
- File length: 349 lines (ticket estimate 400 / 600 / 900). No merged file changed; `RBM3D/Test/Axioms.lean` untouched (the pre-check shows the premise list identical with and without the new import; theorem count 8185 -> 8190).
- Instances (I1)-(I5): `d = 3`, `L = 4`; (I2), (I4) first and (I5) at the merged flow point (`flowP_data.2.2`, `g0P_pos`); (I3), (I4) second at `(g, E) = (10, 63)` with `baSelf_none_of_gt` (side goal `2 + 2·3·|10| < |63|` by `norm_num`); no hypothesis is left open, no hypothesis of another gate is used. (I5) uses constant sequences `zs = EP`, `ms = m0P` at the nondegenerate point.
- The numerical script of section (a) was not re-run by the prover; the instance values (`g0P`, `EP`, `m0P`) enter only as the merged definitions.

## (c) Verified Mathlib names (script: `env.contains` in a scratch file importing `RBM3D.BA.Boundary`; `true` = present)
```
HasStrictDerivAt.localInverse true | HasStrictDerivAt.eventually_right_inverse true | HasStrictDerivAt.eventually_left_inverse true | 
HasStrictDerivAt.to_localInverse true | HasStrictDerivAt.hasDerivAt true | hasStrictDerivAt_inv true | hasStrictDerivAt_id true | 
HasStrictDerivAt.comp true | HasStrictDerivAt.fun_sum true | HasStrictDerivAt.const_mul true | HasStrictDerivAt.const_add true | 
HasStrictDerivAt.const_sub true | Filter.frequently_iff_seq_forall true | Filter.Frequently.and_eventually true | Filter.not_eventually true | 
tendsto_subseq_of_bounded true | Metric.isBounded_closedBall true | mem_closedBall_zero_iff true | tendsto_finsetSum true | Filter.Tendsto.inv₀ true 
| Filter.Tendsto.div_const true | Filter.Tendsto.const_mul true | tendsto_nhdsWithin_iff true | self_mem_nhdsWithin true | 
Filter.Eventually.self_of_nhds true | tendsto_order true | tendsto_nhds_unique true | ge_of_tendsto true | lt_mem_nhds true | inv_anti₀ true | 
Complex.continuous_im true | Complex.abs_im_le_norm true | Complex.norm_natCast true | nhdsWithin_le_nhds true | HasStrictDerivAt.fun_inv false | 
HasStrictDerivAt.inv false | tendsto_finset_sum true | dif_neg true | 
```
Absent (verified `false` above): `HasStrictDerivAt.fun_inv`, `HasStrictDerivAt.inv` (the file composes `hasStrictDerivAt_inv` with `HasStrictDerivAt.comp`). Present but deprecated in this Mathlib (build warning, avoided): `tendsto_finset_sum` (use `tendsto_finsetSum`), `dif_neg` (the file uses `simp [h]`).

## (d) Open issues and paper-delta candidates
- Open issues: none. Every target compiles unconditionally; no hypothesis was added, no target weakened, no signature changed.
- Paper-delta candidates: none new. D471 (T2189a: the identification of `BAm` at real `E` with `m(E + i0)`) is closed by `BAm_tendsto_of_self`, `BAm_im_tendsto_zero`, `BArho_tendsto` and `baMBoundary_holds`; not re-proposed.
- Registry: no line (pre-check above flags nothing).
- For the dispatcher: BA-D7 / BA-C2 consumers get `BASelf_of_tendsto` (closedness), `BAm_tendsto_of_self`, `BArho_tendsto` with the argument orders printed above.
