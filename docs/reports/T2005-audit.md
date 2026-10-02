Auditor model: claude-opus-5-5

# T2005 audit (round 1) — Fri Oct  2 21:58:14 UTC 2026

Branch `t/T2005` at `6533c7c`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2005-audit1` (detached).
Target: `RBM.msc_eq_integral` in `RBM3D/Defs/SemicircleIntegral.lean`. Verdict: **PASS**.

## 1. Statement vs pin

Textual (whitespace-normalised, python regex on the check file and the branch file):
```
msc z = ∫ x in (-2 : ℝ)..2, ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)
msc z = ∫ x in (-2 : ℝ)..2, ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)
EQUAL
```
Binder/hypothesis part in the file: `theorem msc_eq_integral {z : ℂ} (hz : 0 < z.im) :`; pin: `∀ {z : ℂ}, 0 < z.im → …`.

By elaboration (`lake env lean <scratchpad>/audit2005.lean` in the audit worktree; the file copies the pin
`T2005Check.Stmt` verbatim as `T2005AuditStmt` and contains `example : T2005AuditStmt := @RBM.msc_eq_integral`):
```
@RBM.msc_eq_integral : ∀ {z : ℂ}, 0 < z.im → RBM.msc z = ∫ (x : ℝ) in -2..2, ↑(√(4 - x ^ 2) / (2 * Real.pi)) / (↑x - z)
'RBM.msc_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
def RBM.msc : ℂ → ℂ :=
fun z => if 0 < (RBM.mscRoot₁ z).im then RBM.mscRoot₁ z else RBM.mscRoot₂ z
rc=0
```
The pin-typed `example` compiles: the statement is exactly the pin.

Against the paper (`paper/tex/1_2_Intro_model_result.tex`):
```
332: \rho_{\mathrm{sc}}(x) = \sqrt{(4 - x^2)_+}/{2\pi}.
339: m(z)\equiv m_{\mathrm{sc}}(z):=\frac{-z+\sqrt{z^2-4}}{2}= \int_{\mathbb{R}} \frac{\rho_{\mathrm{sc}}(x)}{x - z} \dd x.
```
Hypothesis `0 < z.im` is the paper's `z ∈ ℂ_+`; normalisation `(2π)⁻¹` matches; no losses, exponents, dimensions
or windows are involved. The full general statement is proved (not a special case or adapter).

## 2. Vacuity, hidden hypotheses, cycles

```
$ grep -nE "^(theorem|lemma|def|private|example|noncomputable|abbrev|instance|axiom|@\[)|sorry|admit|native_decide|#print|set_option" RBM3D/Defs/SemicircleIntegral.lean
31:private theorem semicircleIntegral_sub_ne {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
39:private noncomputable def semicircleIntegral_k (z : ℂ) (θ : ℝ) : ℂ :=
42:private theorem semicircleIntegral_k_continuous {z : ℂ} (hz : 0 < z.im) :
48:private theorem semicircleIntegral_subst {z : ℂ} (hz : 0 < z.im) :
98:private theorem semicircleIntegral_fold {z : ℂ} (hz : 0 < z.im) :
116:private theorem semicircleIntegral_contour {z : ℂ} (hz : 0 < z.im) :
189:theorem msc_eq_integral {z : ℂ} (hz : 0 < z.im) :
221:example : msc I = ∫ x in (-2 : ℝ)..2,
226:example : ∫ x in (-2 : ℝ)..2,
```
No structures, no class/hypothesis bundles; the only hypothesis is `0 < z.im` (satisfiable, e.g. `z = I`).
Dependencies outside the file: only `import RBM3D.Defs.Semicircle` (merged on `main`) and Mathlib; the proof body
calls `msc_mul`, `msc_im_pos` (merged). No cycle. All helpers are `private` (CLAUDE.md §3 (E)).
No external hypothesis, so no limit check is needed.

## 3. Compiled nonempty instance

```
221: example : msc I = ∫ x in (-2 : ℝ)..2,
222:     ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - I) :=
223:   msc_eq_integral (by simp)
```
This is the ticket's required instance verbatim; `z = I` (`Im = 1`), hypothesis discharged by `simp`, nondegenerate.
A second example (lines 226–255) evaluates the integral at `z = I` to `I * ((√5 - 1)/2)`. Both are in the built module.

## 4. Build, axioms, hygiene, diff scope

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2005-audit1 && lake build RBM3D.Defs.SemicircleIntegral 2>&1 | grep -E "error|warning|Build|✔.*SemicircleIntegral"
✔ [2986/2986] Built RBM3D.Defs.SemicircleIntegral (8.5s)
Build completed successfully (2986 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Defs/SemicircleIntegral.lean; echo grep_rc=$?
grep_rc=1
$ git diff --name-only main...t/T2005
RBM3D/Defs/SemicircleIntegral.lean
$ git diff --stat main...t/T2005 -- RBM3D/Defs/Semicircle.lean RBM3D.lean; echo rc=$?
rc=0
```
Axioms (section 1): `[propext, Classical.choice, Quot.sound]`. Only the sole writable file is touched;
no frozen signature changed. No errors or warnings in the build output.

## 5. Paper deltas

The prove report proposes none. Audit check: the paper integrates `√((4-x²)_+)/(2π(x-z))` over `ℝ`; Lean integrates
`Real.sqrt (4-x²)/(2π(x-z))` over `[-2,2]`. `Real.sqrt` of a negative is `0`, so the integrand is the paper's
integrand, and it vanishes off `[-2,2]`: the two integrals are equal by definition of the support. No statement
difference; no delta needed. The branch of `√(z²-4)` in `m(z)` is fixed by `msc` (`Im m > 0`) in the merged
`Semicircle.lean`, outside this ticket's scope.

## Observations (no effect on verdict)

- The ticket's "219 lines, read at `c9a24cf`" is internally inconsistent (prove report: 219 = RBM2D HEAD,
  255 = `c9a24cf`); the port citation in the prove report uses `c9a24cf` with the required `diff --stat`.
- Prove report section (c): "Verified absent: none checked" — fine, no absent names were relied on.

## Verdict

- `RBM.msc_eq_integral`: **PASS**. Statement equals the pin and `(eq:defmzsc)`; nonempty instance at `z = I`
  compiles; module builds; standard axioms only; diff confined to the sole writable file. No dispatcher sign-off needed.
