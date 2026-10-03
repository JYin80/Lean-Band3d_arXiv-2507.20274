Auditor model: claude-opus-5-5

# T2011 audit (round 1): PT-B2, bounds of the 1D heat kernel on ℤ

Audit time: Sat Oct  3 01:55:00 UTC 2026 (`date -u`). Audited commit `92a174c` (branch `t/T2011`), detached worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2011-audit1`. `$F` = `RBM3D/Propagator/HeatBounds1D.lean`,
`$SP` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/audit2011`.

## 1. Statement against the pin

Text diff (`$SP/pindiff.py`: regex-extracts `def Bound/Diff1/Diff2 : Prop :=` bodies from
`docs/tickets/checks/T2011-check.lean` and the `theorem … : … := by` types from `$F`, collapses whitespace, compares):
```
$ python3 $SP/pindiff.py
Bound vs hkZ_le identical: True
Diff1 vs hkZ_diff1_le identical: True
Diff2 vs hkZ_diff2_le identical: True
```
Elaboration check (`$SP/AuditPin.lean` = `import RBM3D.Propagator.HeatBounds1D` + the check file's
`namespace RBM.Heat.T2011Check … end` block verbatim + `example : Bound := RBM.Heat.hkZ_le`, same for `Diff1`, `Diff2`,
+ `#print axioms`):
```
$ lake env lean $SP/AuditPin.lean
'RBM.Heat.hkZ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ_diff1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkZ_diff2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
The statements (extracted from `$F`) are, for all three: `∃ C c, 0 < C ∧ 0 < c ∧ ∀ τ > 0, ∀ n : ℤ, …` with gains
`min 1 (τ ^ (-(1/2)))`, `min 1 τ⁻¹`, `min 1 (τ ^ (-(3/2)))` and the common factor `exp (-c * min (n²/τ) |n|)`;
the differences are `h(n+1) − h(n)` and `h(n+1) + h(n−1) − 2h(n)`. Constants precede `∀ τ ∀ n` (uniform in `τ, n`),
as the ticket's mathematics requires. No extra hypothesis; the only hypothesis is `0 < τ`.
`hkZ` is the merged definition (`RBM3D/Propagator/HeatKernel1D.lean:128`, merged 73cf5c1):
```
noncomputable def hkZ (τ : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-2 * τ) * ∑' j : ℕ, τ ^ j * (walkCount j n : ℝ) / (Nat.factorial j : ℝ)
```

## 2. Vacuity, hidden hypotheses, cycles

```
$ grep -cE "^(private )?(structure|class) " $F
0
$ grep -nE "^(protected )?(theorem|lemma|def|abbrev|noncomputable def|instance|structure|class) " $F
635:theorem hkZ_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
670:theorem hkZ_diff1_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
734:theorem hkZ_diff2_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℤ,
$ grep -nE "hkZ_(tilt|nonneg|mass|neg|hasSum_mgf)" $F
20:inversion formula `hkZ_tilt` (no contour shift, no Poisson measure, no Bessel function):
124:/-- The tilted integrand `exp (2τ (cosh (ν + ik) - 1))` of `hkZ_tilt`. -/
161:  hkZ_tilt τ hτ ν m
```
No structure/class, no hypothesis `Prop`, no external input (DECISIONS §16 respected). The only upstream dependency is the
merged theorem `hkZ_tilt` (commit 73cf5c1 on `main`); no cycle. All 40 helpers are `private` (§3 (E)).
The `∃ C c` with `0 < C`, `0 < c` is non-vacuous: the proof gives explicit witnesses (e.g. `hkZ_le`, line 637:
`refine ⟨max 1 ((2 * Real.pi)⁻¹ * (1 * (2 * Real.sqrt (2 * Real.pi)))), 1 / 8, …`), and `c > 0` makes the decay real.

## 3. Compiled nonempty instances

`$F`, section `Compiled instances` (lines ~800–871), six `example`s, all at `τ = 100` (hypothesis `0 < 100` discharged by
`norm_num`), each obtained by `obtain ⟨C, c, hC, hc, h⟩ := <target>` and `h 100 (by norm_num) n`:
```
example : ∃ C : ℝ, hkZ 100 0 ≤ C * (1 / 10)                                      -- hkZ_le, n = 0
example : ∃ C : ℝ, |hkZ 100 1 - hkZ 100 0| ≤ C / 100                             -- hkZ_diff1_le, n = 0
example : ∃ C : ℝ, |hkZ 100 1 + hkZ 100 (-1) - 2 * hkZ 100 0| ≤ C / 1000         -- hkZ_diff2_le, n = 0
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ hkZ 100 7 ≤ C * (1 / 10) * Real.exp (-(c * (49 / 100)))
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ |hkZ 100 8 - hkZ 100 7| ≤ C / 100 * Real.exp (-(c * (49 / 100)))
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    |hkZ 100 8 + hkZ 100 6 - 2 * hkZ 100 7| ≤ C / 1000 * Real.exp (-(c * (49 / 100)))
```
The three ticket-required instances are present verbatim in the ticket's form; the `n = 7` ones exercise the
exponential factor nontrivially. Data are nondegenerate (`τ = 100`, `n ∈ {0, 7}`); every hypothesis is discharged.
They compile (build in §4 and fresh elaboration below).

## 4. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Propagator.HeatBounds1D 2>&1 | grep -E "error|warning|Build|Built RBM3D.Propagator.HeatBounds1D"
✔ [3387/3387] Built RBM3D.Propagator.HeatBounds1D (7.3s)
Build completed successfully (3387 jobs).
$ lake env lean RBM3D/Propagator/HeatBounds1D.lean 2>&1 | grep -E "error|warning|sorry"   # fresh elaboration
exit=0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom" $F; echo "exit=$?"
exit=1
$ git diff --name-only main...t/T2011
RBM3D/Propagator/HeatBounds1D.lean
$ git diff main...t/T2011 -- RBM3D/Propagator/HeatKernel1D.lean RBM3D.lean | wc -l
       0
$ grep -rnE "\b(hkZ_le|hkZ_diff1_le|hkZ_diff2_le)\b" RBM3D --include='*.lean' | grep -v HeatBounds1D; echo "exit=$?"
exit=1
```
Axioms (from §1): only `propext`, `Classical.choice`, `Quot.sound` for all three targets. Imports: 
`RBM3D.Propagator.HeatKernel1D` and six Mathlib files; not `RBM3D` (as the ticket requires). The diff touches only the
sole writable file; no frozen signature changed; no name clash. (Full `lake build` is run by the hub at merge.)

## 5. Paper deltas

The targets are route-H auxiliary lemmas (design T2003 row S3, Fable S3-Z), not statements of the paper; the ticket
expects no paper-delta candidate, and the prove report proposes none. No Lean/paper statement difference to cover.

## Observations (no effect on verdict)

- O1. The ticket-required `n = 0` instances have the shape `∃ C, X ≤ C·r`, which holds for any real `X`; they do apply
  the theorems with all hypotheses discharged, and the additional `n = 7` instances keep `0 < C ∧ 0 < c`. Ticket design
  point, not a defect of the submission.
- O2. The proved constants are `(1, 1/8)`, `(≈12.42, 1/16)`, `(≈517.03, 1/16)` (read from the `refine ⟨max …⟩` lines),
  not Fable's `c₀ = 0.18/0.14` or the dispatcher's `C = 1, c = 0.09`; the pins leave `C, c` existential, so this is
  inside the pin. Downstream tickets needing explicit constants need a primed explicit lemma (prove report (d)).
- O3. Gaussian/tilt helper lemmas are `private`; downstream reuse needs an amend (prove report (d)).

## Verdict

| Target | Statement | Vacuity / hidden hyp. / cycle | Instance | Build / axioms | Paper deltas | Verdict |
|---|---|---|---|---|---|---|
| `RBM.Heat.hkZ_le` (Bound) | identical to pin | none | compiled, τ=100, n∈{0,7} | ok / 3 std | none needed | **PASS** |
| `RBM.Heat.hkZ_diff1_le` (Diff1) | identical to pin | none | compiled, τ=100, n∈{0,7} | ok / 3 std | none needed | **PASS** |
| `RBM.Heat.hkZ_diff2_le` (Diff2) | identical to pin | none | compiled, τ=100, n∈{0,7} | ok / 3 std | none needed | **PASS** |

Ticket T2011: **PASS**. No dispatcher sign-off needed.
