Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  2 21:53:56 UTC 2026

Target: for `Im z > 0`, `msc z = ∫_{-2}^{2} ρ(x)/(x - z) dx`, `ρ(x) = √(4-x²)/(2π)` (paper `eq:defmzsc`, `paper/tex/1_2_Intro_model_result.tex:339-340`). Here `msc z` is the root of `m² + z m + 1 = 0` with `Im m > 0` (`RBM3D/Defs/Semicircle.lean:116`; `msc_mul`: `m(m+z) = -1`).

### (i) Exponent / constant table

Route (the ported RBM2D proof): `x = 2cosθ` (`dx = -2 sinθ dθ`, `x: -2→2` is `θ: π→0`), `k(θ) = (2cosθ - z)⁻¹`, `J = ∫_0^π k`, `m = msc z`, `r₁ = -m`, `r₂ = -m⁻¹`.

| # | Constant / identity | Value | Constraint it must satisfy | Slack / check |
|---|---|---|---|---|
| 1 | normalization of `ρ` | `(2π)⁻¹` | `∫ρ = 1`, matches paper `ρ_sc = √((4-x²)_+)/(2π)` | exact; on `[-2,2]` `(4-x²)_+ = 4-x²` |
| 2 | `√(4 - 4cos²θ)` for `θ ∈ [0,π]` | `2 sinθ` | needs `sinθ ≥ 0` | holds on `[0,π]`, equality at endpoints only |
| 3 | integrand after substitution | `2 sinθ · (2 sinθ/(2π)) / (2cosθ - z) = (2/π) sin²θ · k(θ)` | factor `2/π` = `2` (from `dx`) × `(2π)⁻¹ · 2` | exact |
| 4 | polynomial division with `c = 2cosθ`: `sin²θ = 1 - c²/4` | `sin²θ·k = -(½)cosθ - z/4 + (1 - z²/4) k` | `1 - c²/4 = -(c-z)(c+z)/4 + (1 - z²/4)` | exact identity |
| 5 | `∫_0^π (-(½)cosθ - z/4) dθ` | `-πz/4` | `∫_0^π cos = 0` | exact |
| 6 | substituted integral | `(2/π)(-πz/4 + (1 - z²/4) J)` | rows 3–5 | numerics below (`subst formula`) |
| 7 | fold `∫_0^{2π} k = 2J` | `2` | `cos(2π-θ)=cos θ` | exact; numerics below |
| 8 | Cauchy on `|w|=1`, `w = e^{iθ}`, `2cosθ = w + w⁻¹` | `∫_0^{2π} k dθ = 2π (r₁-r₂)⁻¹` | `(w-r₁)(w-r₂) = w(2cosθ - z)`, `r₁+r₂ = z`, `r₁r₂ = 1`; `dw = i w dθ` | `r₁+r₂=z`: `-m-m⁻¹ = z` follows from `msc_mul`; `r₁r₂=1` exact |
| 9 | residue location | `r₁ = -m` inside, `r₂ = -m⁻¹` outside | `‖m‖ < 1` (`norm_msc_lt_one`), `m ≠ 0` (`msc_im_pos`) | `‖r₁‖ = ‖m‖ < 1`, `‖r₂‖ = ‖m‖⁻¹ > 1`: `|r₁|,|r₂|` = 0.618, 1.618 at `z=i`; 0.9497, 1.0530 at `z=0.5+0.1i` |
| 10 | residue at `-m` | `(r₁ - r₂)⁻¹ = (-m + m⁻¹)⁻¹ = m/(1-m²)` | `1 - m² ≠ 0` (else `m = ±1`, `Im m = 0`, contradicts `Im m > 0`) | nonzero; `r₁ ≠ r₂` since `‖r₁‖<1<‖r₂‖` |
| 11 | `J = π (-m + m⁻¹)⁻¹` | from rows 7–8: `2J = 2π (r₁-r₂)⁻¹` | — | numerics below (`J vs`) |
| 12 | closure: `z = -m - m⁻¹`, `1 - z²/4 = -(1-m²)²/(4m²)`, `-z/4 = (m²+1)/(4m)` | `2[(m²+1)/(4m) - (1-m²)/(4m)] = 2·(2m²)/(4m) = m` | field identity, `m ≠ 0`, `1-m² ≠ 0`, `π ≠ 0` | exact (hand computation) |
| 13 | integrand continuity on `[-2,2]` | `x - z ≠ 0` for real `x` | `Im z > 0` | `|Im(x-z)| = Im z > 0`, uniform margin `Im z` |

No threshold or exponent is involved. The hypothesis `0 < Im z` is used at rows 9, 10, 13; nothing else is needed. Names `msc_mul`, `msc_im_pos`, `norm_msc_lt_one`, `mscDisc_sq` are in the merged `RBM3D/Defs/Semicircle.lean` (lines 118, 123, 152, 105); the proof body below uses only the first three. RBM3D defs `mscDisc/mscRoot₁/mscRoot₂/msc` are at `Semicircle.lean:102-116`.

### (ii) Concrete nondegenerate instance and check

Instances: `z = i` (`Im = 1`) and `z = 0.5 + 0.1 i` (`Im = 0.1`). Script (Gauss-Legendre with 4000 nodes in `θ` for the smooth integrands; independent raw midpoint rule in `x` with 2·10⁶ nodes against the root formula; python3/numpy 2.0.2, no Lean):

```
$ python3 <scratchpad>/chk.py      # scratchpad = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad
z= 1j
 msc root formula   : 0.6180339887498949j  |m|= 0.6180339887498949  Im m= 0.6180339887498949
 integral (x=2cos t): 0.6180339887496399j  |diff|= 2.5501822875639846e-13
 subst formula      : (6.938893903907228e-17+0.6180339887496401j)  |diff|= 2.547961935998582e-13
 fold 2J vs int_0^2pi: 1.0370441935377456e-12
 J vs pi/(-m+1/m)   : 3.2018833217501175e-13
 contour 2pi/(r1-r2): 1.2161740868987853e-12
 r1+r2=z: 2.220446049250313e-16  r1*r2=1: 0.0  |r1|= 0.6180339887498949  |r2|= 1.6180339887498947
 raw x midpoint     : (-9.472600481785775e-17+0.6180339887718228j)  |diff|= 2.1927903937273606e-11
z= (0.5+0.1j)
 msc root formula   : (-0.23710837400499216+0.9196216757172846j)  |m|= 0.9496970082465026  Im m= 0.9196216757172846
 integral (x=2cos t): (-0.2371083740048941+0.9196216757169051j)  |diff|= 3.9193946303549957e-13
 subst formula      : (-0.23710837400489412+0.9196216757169049j)  |diff|= 3.9214751015557565e-13
 fold 2J vs int_0^2pi: 1.3806282008436848e-12
 J vs pi/(-m+1/m)   : 6.553174349072183e-13
 contour 2pi/(r1-r2): 2.1326750959739994e-12
 r1+r2=z: 8.326672684688674e-17  r1*r2=1: 1.150171226193536e-16  |r1|= 0.9496970082465026  |r2|= 1.052967410991823
 raw x midpoint     : (-0.2371083739905003+0.9196216757205862j)  |diff|= 1.486318329729559e-11
```

Reading: `integral` (substitution form), `subst formula` (row 6), `fold`, `J vs`, `contour` (row 8) and `raw x midpoint` all agree with the root-formula `msc z` to 1e-12 or better (raw midpoint to 2e-11, limited by the `√` endpoint singularity). `|r₁|<1<|r₂|` at both points. At `z = i`, `msc i = i(√5-1)/2 = 0.6180339887…i`, matching the table. Every hypothesis (`Im z > 0`; `Im m > 0`; `‖m‖ < 1`; `m ≠ 0`; `1-m² ≠ 0`) holds at both points, with no degenerate quantity.

No external hypothesis (only merged `RBM3D/Defs/Semicircle.lean` facts), so no limit computation is needed.

### Observations for stage 1b (non-mathematical facts from the tool log)

```
$ git -C ../RBM2D --no-optional-locks diff --stat 99d6fe0 c9a24cf -- RBM2D/Defs/SemicircleIntegral.lean
 RBM2D/Defs/SemicircleIntegral.lean | 36 ++++++++++++++++++++++++++++++++++++
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Defs/SemicircleIntegral.lean
 RBM2D/Defs/SemicircleIntegral.lean | 36 ------------------------------------
$ wc -l ../RBM2D/RBM2D/Defs/SemicircleIntegral.lean ; git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Defs/SemicircleIntegral.lean | wc -l
     219 ...    # RBM2D HEAD 0c1330a (line 219)
     255        # at c9a24cf
```
The 36-line difference is, per `git diff c9a24cf HEAD`, only the `example`s and `#print axioms` after `/-! ### Check at `z = i` -/`; the theorem and all private steps are unchanged. The ticket's "219 lines, read at c9a24cf" does not match: 219 lines is RBM2D HEAD, 255 lines is `c9a24cf`. Cite file:line from the version actually read.

### Verdict

- `msc_eq_integral`: **PASS**. Every constant in the table closes exactly (hand computation rows 4–12) and numerically at both test points; hypothesis set `0 < z.im` is satisfiable (z = i) and nondegenerate; the ported proof needs only `msc_mul`, `msc_im_pos`, `norm_msc_lt_one`, all merged; the final `field_simp; ring` in the port is the row 12 identity.

## (b) Script output — Fri Oct  2 21:56 UTC 2026 (stage 1b)

Commit on `t/T2005`: `6533c7c` (only `RBM3D/Defs/SemicircleIntegral.lean`, 255 lines).

```
$ cd ../RBM3D-wt/T2005 && lake build RBM3D.Defs.SemicircleIntegral 2>&1 | tail -3
✔ [2986/2986] Built RBM3D.Defs.SemicircleIntegral (8.0s)
Build completed successfully (2986 jobs).

$ lake env lean <scratchpad>/ax.lean     # import RBM3D.Defs.SemicircleIntegral; #print axioms RBM.msc_eq_integral
'RBM.msc_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]

$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Defs/SemicircleIntegral.lean ; echo rc=$?
rc=1                                       # (no match)

$ git diff --stat main...t/T2005
 RBM3D/Defs/SemicircleIntegral.lean | 255 +++++++++++++++++++++++++++++++++++++
 1 file changed, 255 insertions(+)

$ grep -rn "msc_eq_integral\|semicircleIntegral\|SemicircleIntegral_" RBM3D | grep -v "Defs/SemicircleIntegral.lean" ; echo rc=$?
rc=1                                       # name clash: none
```

Target statement, extracted from the file (`SemicircleIntegral.lean:189-191`):

```
theorem msc_eq_integral {z : ℂ} (hz : 0 < z.im) :
    msc z = ∫ x in (-2 : ℝ)..2,
      ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z) := by
```

Pin comparison (python, whitespace-normalised; text after `msc z = ` in `docs/tickets/checks/T2005-check.lean` vs the file):

```
∫ x in (-2 : ℝ)..2, ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)
∫ x in (-2 : ℝ)..2, ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)
EQUAL
```

Compiled instance at `z = i` (`SemicircleIntegral.lean:221-223`, inside the built file; no hypothesis left open):

```
example : msc I = ∫ x in (-2 : ℝ)..2,
    ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - I) :=
  msc_eq_integral (by simp)
```

The file also keeps RBM2D's second example (lines 226-): the integral at `z = i` equals `I * ((√5 - 1)/2)`.

Port: RBM2D `RBM2D/Defs/SemicircleIntegral.lean` at commit `c9a24cf` (255 lines; the ticket's "219 lines" is RBM2D HEAD `0c1330a`; the 36 extra lines at `c9a24cf` are the two `example`s and `#print axioms`). Source lines: private steps from line 30, theorem at line 187, examples from line 219.

```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf
c9a24cf
$ git -C ../RBM2D --no-optional-locks diff --stat 99d6fe0 c9a24cf -- RBM2D/Defs/SemicircleIntegral.lean
 RBM2D/Defs/SemicircleIntegral.lean | 36 ++++++++++++++++++++++++++++++++++++
 1 file changed, 36 insertions(+)
```

Narrative. The port is textual. Changes: `import RBM2D.Defs.Semicircle` became `import RBM3D.Defs.Semicircle`; docstring references to the RBM2D file and `(1-2:115)` replaced by RBM3D file and `eq:defmzsc` (`1_2_Intro_model_result.tex:337-340`); the trailing `#print axioms` removed. The proof body is unchanged. It uses only `msc_mul`, `msc_im_pos`, `norm_msc_lt_one` from `RBM3D/Defs/Semicircle.lean`. No dimension-specific content (the file is d-free). All helpers are `private` or prefixed `semicircleIntegral_` (CLAUDE.md §3 (E)).

## (c) Verified Mathlib names used (all compile in the built file)

`intervalIntegral.integral_deriv_smul_comp`, `intervalIntegral.integral_comp_sub_left`, `intervalIntegral.integral_add_adjacent_intervals`, `intervalIntegral.integral_ofReal`, `integral_cos`, `DiffContOnCl.circleIntegral_sub_inv_smul`, `deriv_circleMap`, `Complex.two_cos`, `Complex.sin_sq_add_cos_sq`, `Real.cos_two_pi_sub`, `Real.sin_nonneg_of_nonneg_of_le_pi`, `one_lt_inv₀`, `sq_eq_one_iff`. Verified absent: none checked.

## (d) Open issues and paper-delta candidates

- No Lean/paper statement difference: `msc_eq_integral` is `(eq:defmzsc)` with `ρ_sc(x) = √(4-x²)/(2π)` on `[-2,2]`, where `(4-x²)_+ = 4-x²`.
- Ticket text nit (not a statement issue): "219 lines, read at `c9a24cf`" is inconsistent (219 = RBM2D HEAD, 255 = `c9a24cf`). No paper-delta candidates (`T2005a`: none).
