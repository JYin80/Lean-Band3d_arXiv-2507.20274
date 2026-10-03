Auditor model: claude-opus-5-5

# T2017 audit (round 1) — PT-C, 1D torus heat kernel bounds

Written Sat Oct  3 03:10:55 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2017-audit1`, detached at `t/T2017` = `c6a31ce`.
Scratch Lean files live in the session scratchpad (`$S`); none is in the repository.

## 1. Diff scope and hygiene

```
$ git diff --name-only main...t/T2017
RBM3D/Propagator/HeatTorus1D.lean
$ git diff main...t/T2017 -- RBM3D.lean RBM3D/Test | wc -l
       0
$ git merge-base main t/T2017 ; git log -1 --format=%h main
868b3b47d472f4af3777162206eb43ee5c979dda
b64efda
$ git diff --stat 868b3b4 main -- RBM3D/Propagator/HeatBounds1D.lean RBM3D/Propagator/HeatKernel1D.lean RBM3D/Defs/Lattice.lean
(empty: upstream files unchanged on main since the merge base)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option|implemented_by|extern|unsafe|opaque" RBM3D/Propagator/HeatTorus1D.lean; echo grep-exit=$?
grep-exit=1
$ grep -nE "^(noncomputable )?(theorem|lemma|def|abbrev|instance|structure|class)" HeatTorus1D.lean   (non-private)
218:theorem hkT_le ...   240:theorem hkT_diff1_le ...   266:theorem hkT_diff2_le ...   608:theorem hkT_gap ...
$ grep -c "^private" RBM3D/Propagator/HeatTorus1D.lean
19
```
Only the sole writable file is touched; no structure, class or new hypothesis `Prop` (DECISIONS §16).

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.Propagator.HeatTorus1D 2>&1 | grep -iE "error|warning|sorry|Build completed"
Build completed successfully (3390 jobs).
EXIT=0
$ lake env lean $S/T2017_pins.lean     (pins copied from the check file + checks below + #print axioms)
'RBM.Heat.hkT_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkT_diff1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkT_diff2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.hkT_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```
`T2017_pins.lean` contains, for each (pin, theorem) pair, `example : Pin = (type_of% @RBM.Heat.thm) := rfl` and `example : Pin := RBM.Heat.thm`; all elaborated (EXIT=0).

## 3. Statements against the pins (script diff)

```
$ python3 (pin body from docs/tickets/checks/T2017-check.lean vs theorem type up to ":= by", whitespace-normalised)
TorusBound hkT_le text-identical: True
TorusDiff1 hkT_diff1_le text-identical: True
TorusDiff2 hkT_diff2_le text-identical: True
TorusGap hkT_gap text-identical: True
$ lake env lean $S/T2017_expr.lean     (run_cmd: pin `defnInfo.value == theorem.type`)
TorusBound vs hkT_le: Expr-identical = false
TorusDiff1 vs hkT_diff1_le: Expr-identical = true
TorusDiff2 vs hkT_diff2_le: Expr-identical = false
TorusGap vs hkT_gap: Expr-identical = false
$ (same file, pp.all, first differing token)
TorusBound: pin `RBM.Heat.T2017Check.TorusBound._proof_1` / thm `(@Nat.instAtLeastTwoHAddOfNat ...`
TorusDiff2: pin `RBM.Heat.T2017Check.TorusBound._proof_1` / thm `(@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) ...`
TorusGap:   pin `RBM.Heat.T2017Check.TorusBound._proof_1` / thm `(@Nat.instAtLeastTwoHAddOfNat ...`
```
The only Expr difference is the proof of the `Prop` instance `Nat.AtLeastTwo 2` (used by the numeral `2` in `^ 2`):
the `def` pins abstract it into the auxiliary constant `TorusBound._proof_1`, the theorem types inline it.
By proof irrelevance the statements are the same, and the `rfl` checks of §2 confirm it. Source text is identical.

Upstream signatures used (no hypotheses beyond those shown; all merged on main, axioms standard):
```
RBM.Heat.hkT : (L : ℕ) → [NeZero L] → ℝ → ZMod L → ℝ
  := fun L τ x => (↑L)⁻¹ * ∑ k, Real.cos (2π k.val x.val / L) * Real.exp (-2 τ (1 - Real.cos (2π k.val / L)))
RBM.Heat.hkT_hasSum_images : ∀ L [NeZero L] τ, 0 ≤ τ → ∀ x, HasSum (fun y => hkZ τ (↑x.val + ↑L * y)) (hkT L τ x)
RBM.Heat.hkZ_le / hkZ_diff1_le / hkZ_diff2_le : ∃ C c, 0 < C ∧ 0 < c ∧ ∀ τ, 0 < τ → ∀ n : ℤ, ... (no other hypotheses)
RBM.zdist : (L : ℕ) → ZMod L → ℕ := fun L u => min u.val (L - u.val)
'RBM.Heat.hkZ_diff2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Statement check against the ticket's mathematics (Fable F3 / S3-L), per target:
- `hkT_le` (TorusBound): `∃ C c > 0`, then `∀ L [NeZero L] τ, 0 < τ → τ ≤ L² → ∀ x`; bound `C min(1, τ^{-1/2}) e^{-c min(|x|_L²/τ, |x|_L)}`. Constants come before `L, τ, x` (uniform), as in the ticket. Matches.
- `hkT_diff1_le` (TorusDiff1): forward difference `x+1` vs `x`, loss `min(1, τ^{-1})`, same exponent and range. Matches.
- `hkT_diff2_le` (TorusDiff2): symmetric second difference, loss `min(1, τ^{-3/2})`, same range. Matches.
- `hkT_gap` (TorusGap): `∀ L τ, L² ≤ τ → ∀ x`, three conjuncts with `L^{-1}`, `L^{-2}`, `L^{-3}` and `e^{-cτ/L²}`, uniform `(C, c)`. Matches.
No hypothesis is weakened or added; the range `τ ≤ L²` / `τ ≥ L²` is the ticket's split, and `L` is unrestricted (`NeZero L`), so `L = 1, 2` are covered as the ticket asks.

## 4. Vacuity, hidden hypotheses, cycles

- No hypothesis `Prop`, no structure field: the targets are closed `∃`-statements whose only premises are `0 < τ`, `τ ≤ L²` (resp. `L² ≤ τ`) and `NeZero L`, all satisfiable (instances below).
- The conclusion is not trivial: `C, c > 0` are required, and the proved theorems were checked to inhabit the pins exactly.
- Dependencies: `hkT`, `hkT_hasSum_images` (HeatKernel1D), `hkZ_le`, `hkZ_diff1_le`, `hkZ_diff2_le` (HeatBounds1D), `zdist` (Defs/Lattice) — all merged on main (unchanged since the merge base, §1). The new file imports only `RBM3D.Propagator.HeatBounds1D`, `RBM3D.Defs.Lattice` and three Mathlib files; no cycle. No external input.

## 5. Compiled nonempty instances (in the file, lines 727–758; built in §2)

```
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ hkT 5 4 2 ≤ C * min 1 ((4 : ℝ) ^ (-(1 / 2 : ℝ))) * Real.exp (...)
  obtain ⟨C, c, hC, hc, h⟩ := hkT_le;       exact ⟨C, c, hC, hc, h 5 4 (by norm_num) (by norm_num) 2⟩
example : ... |hkT 5 4 (2 + 1) - hkT 5 4 2| ≤ ...                     -- hkT_diff1_le, same arguments
example : ... |hkT 5 4 (2 + 1) + hkT 5 4 (2 - 1) - 2 * hkT 5 4 2| ≤ ... -- hkT_diff2_le, same arguments
example : ... (three conjuncts at L = 5, τ = 50, x = 2)
  obtain ⟨C, c, hC, hc, h⟩ := hkT_gap;      exact ⟨C, c, hC, hc, h 5 50 (by norm_num) 2⟩
```
Data: `L = 5`, `x = 2` (`zdist 5 2 = 2`), `τ = 4` (`0 < 4 ≤ 25`) and `τ = 50` (`25 ≤ 50`), exactly the ticket's prescribed instances.
Every deterministic hypothesis (`0 < τ`, `τ ≤ L²`, `L² ≤ τ`) is discharged by `norm_num`; `NeZero 5` by instance. Not degenerate (no `L = 0`, empty index, collapsed window or `False` premise).

## 6. Paper deltas

The four theorem types equal the ticket's pins (§3); the ticket expects no paper-delta candidate and the prove report proposes none (§(d)).
`grep -n T2017 docs/paper-deltas.md` prints nothing, consistent with no candidate. No Lean/ticket statement difference was found, so nothing is uncovered.

## 7. Observations (no effect on statements, instances, build, axioms or delta coverage)

- O1. At `L = 5, τ = 4, x = 2` the first difference equals 0 by symmetry (`3 ≡ −2`, preflight output `D1=0.000000e+00`). The data is the ticket's prescribed instance and is nondegenerate; noted only.
- O2. The constants are existential, as pinned (`C = C_Z · Σ' y e^{-(c_Z/8)|y|}`, `c = c_Z/2`; gap `(1, 4)` per the prove report). Downstream PT-D gets no explicit numbers. This is the ticket's design, not a defect.
- O3. The prove report says the required-reading RBM2D file was not opened and nothing was ported (`grep RBM1D\|RBM2D` gives no match). No port citation is needed.

## Verdicts

| Target | Pin | Statement | Instance | Build/axioms | Verdict |
|---|---|---|---|---|---|
| `hkT_le` | TorusBound | identical (text; Expr up to Prop-proof aux constant; rfl) | L=5, τ=4, x=2 | pass / standard 3 | PASS |
| `hkT_diff1_le` | TorusDiff1 | identical (Expr-identical) | L=5, τ=4, x=2 | pass / standard 3 | PASS |
| `hkT_diff2_le` | TorusDiff2 | identical (text; Expr up to Prop-proof aux constant; rfl) | L=5, τ=4, x=2 | pass / standard 3 | PASS |
| `hkT_gap` | TorusGap | identical (text; Expr up to Prop-proof aux constant; rfl) | L=5, τ=50, x=2 | pass / standard 3 | PASS |

Ticket verdict: **PASS**. No dispatcher sign-off needed. The full `lake build` is left to the hub at merge.
