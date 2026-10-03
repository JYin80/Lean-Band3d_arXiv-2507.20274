Auditor model: claude-opus-5-5

# T2023 audit (round 1) — PT-F1: `prop5Decay_holds`, `prop8ZeroMode_holds`
Written: Sat Oct  3 04:57:11 UTC 2026. Worktree: /Users/junyin/Lean_proof/RBM3D-wt/T2023-audit1 (detached at t/T2023 = 3a5a579).

## 0. Scope
```
$ git diff --name-only main...t/T2023
RBM3D/Propagator/Prop5Hold.lean
$ git merge-base main t/T2023 ; git diff --stat ea34a14 main -- RBM3D/Propagator/ RBM3D/Defs/ RBM3D.lean
ea34a1495e854aa2f4b0d5612445c29328e9db1d
 RBM3D.lean | 6 ++++++        # no imported dependency changed on main since the base
$ grep -n "^import" RBM3D/Propagator/Prop5Hold.lean
6:import RBM3D.Propagator.HeatProduct
7:import RBM3D.Propagator.LaplaceGauss
8:import RBM3D.Propagator.Pins
9:import RBM3D.Propagator.Prop5Short
10:import RBM3D.Propagator.Props4
```
Only the sole writable file; imports as the ticket allows (no `import RBM3D`); `Pins.lean` (frozen pins) untouched.

## 1. Statements against the pins
Pins (`RBM3D/Propagator/Pins.lean:35-43, 88-95`, unchanged by the branch). Script check, `lake env lean ax.lean`:
```
import RBM3D.Propagator.Prop5Hold
#print axioms RBM.prop5Decay_holds
#print axioms RBM.prop8ZeroMode_holds
example : ∀ d Λ, Prop5Decay d Λ := @RBM.prop5Decay_holds
example : ∀ d Λ κ, Prop8ZeroMode d Λ κ := @RBM.prop8ZeroMode_holds
#check @RBM.prop5Decay_holds
#check @RBM.prop8ZeroMode_holds
--- output ---
'RBM.prop5Decay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.prop8ZeroMode_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
prop5Decay_holds : ∀ (d : ℕ) (Λ : ℝ), Prop5Decay d Λ
prop8ZeroMode_holds : ∀ (d : ℕ) (Λ κ : ℝ), Prop8ZeroMode d Λ κ
exit=0
```
The types are exactly the ticket's targets `theorem prop5Decay_holds (d : ℕ) (Λ : ℝ) : Prop5Decay d Λ` and
`theorem prop8ZeroMode_holds (d : ℕ) (Λ κ : ℝ) : Prop8ZeroMode d Λ κ`: no extra arguments, so no added
hypothesis. Quantifier order is the pins' (`3 ≤ d → 0 < Λ [→ 0 < κ] → ∃ C c, ∀ L ≥ 3, g ∈ (0,Λ], t ∈ [0,1),
‖m‖ = 1 [, κ ≤ Im m], σ₁ σ₂, a`); all sign pairs, general `d ≥ 3`, full `t`-range — not a special case.
Pin vs paper (`paper/tex/1_2_Intro_model_result.tex:1144-1146` (prop:ThfadC), `:1165-1167` (prop:ThfadC0)):
`Λ`-dependent constants, P5 for every unit `m`, P8 loss-free (stronger than `≺`), bulk `κ ≤ Im m`, periodic ℓ¹
`|a|` — all differences of the merged pins, covered by T2003a, c, d, e, f (signed, DECISIONS §13).

## 2. Vacuity, hidden hypotheses, cycles
- No structure argument, no `Prop` hypothesis: the theorems take only `d Λ (κ)`. The proof consumes merged
  theorems (`kProd_le`, `kProd_gap`, `lg_bulk`, `lg_convA`, `norm_Theta_apply_le`, `prop5Short_holds`, ...;
  `Prop5Hold.lean:786-790, 1268-1273`) from modules already on main; axioms above are the three standard ones,
  so the chain is fully proved. No cycle (the new file imports only merged modules; nothing imports it).
- No external hypothesis is introduced (DECISIONS §16: none taken), so no limit check is required.
- `sorry/admit/native_decide/axiom` grep:
```
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Propagator/Prop5Hold.lean ; echo grep_exit=$?
grep_exit=1
```

## 3. Compiled nonempty instances (same file, `Prop5Hold.lean:1317-1397`)
Ticket requires: `prop5Decay_holds 3 1`, `prop8ZeroMode_holds 3 1 (1/2)` at `L = 5, g = 1/2, t = 9/10, m = I,
σ₁ = true, σ₂ = false, a = 0`. Present and compiled (module builds, §4):
```
obtain ⟨C, hC, c, hc, H⟩ := prop5Decay_holds 3 1 (by norm_num) (by norm_num)
exact ⟨C, hC, c, hc, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10)
  (by norm_num) (by norm_num) Complex.I Complex.norm_I true false 0⟩
...
obtain ⟨C, hC, H⟩ := prop8ZeroMode_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
  (by norm_num) Complex.I Complex.norm_I (by norm_num) true false 0⟩
```
Every hypothesis (`3 ≤ 3`, `0 < 1`, `0 < 1/2`, `3 ≤ 5`, `0 < 1/2 ≤ 1`, `0 ≤ 9/10 < 1`, `‖I‖ = 1`, `1/2 ≤ Im I`)
is discharged; data nondegenerate (`N = 5^3`, `g, 1-t > 0`). Extra instances also compile: `a = (1,0,0)`
(`zdistD = 1`, by `decide`), P8 with `σ₁ = σ₂ = true` (the `prop5Short_holds` branch), the zero-mode regime
`t = 999/1000` (`ε < L⁻²`) at `a = (2,1,0)`, `|a| = 3`; plus the `Prop5to8` bundle with `Prop6Diff1`/`Prop7Diff2`
as hypotheses (other gates' pins) and the bridges to `ThetaDecay`/`ThetaZeroMode`.

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.Propagator.Prop5Hold 2>&1 | grep -iE "error|warning|Build"
warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Propagator/HeatProduct.lean:218:0: `abs_prod_sub_prod_le` does not use the following hypothesis in its type:
Build completed successfully (3408 jobs).
$ ls -la .lake/build/lib/lean/RBM3D/Propagator/Prop5Hold.olean     # built now (04:55 UTC), absent on main's cache
-rw-r--r--@ 1 junyin  staff  3916808 Oct  2 21:55 .lake/build/lib/lean/RBM3D/Propagator/Prop5Hold.olean
```
No error; no warning in the new file (the two warnings are in merged modules). Merge-time simulation:
```
$ printf 'import RBM3D\nimport RBM3D.Propagator.Prop5Hold\n#assert_rbm_axioms\n' > assert.lean
$ lake build RBM3D 2>&1 | grep -E "error|Build completed"; lake env lean assert.lean
Build completed successfully (3715 jobs).
axiom audit: 987 theorems, 378 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
  RBM.Prop5Decay: 1 [no certificate]
  RBM.Prop8ZeroMode: 1 [no certificate]
exit=0
```
(The single theorem "resting on" each pin is the merged bridge `Prop5Decay.thetaDecay` / `Prop8ZeroMode.thetaZeroMode`
in `Pins.lean`, which takes the pin as an argument; moving the pins out of `borrowedProps` is PT-G's job per the
ticket — `Test/Axioms.lean` is not writable here.)

Public names added: only the two pinned targets; all helpers are `private` (`p5h_*`, `p5hCh`):
```
$ grep -rn "prop5Decay_holds\|prop8ZeroMode_holds" RBM3D/ --include=*.lean | grep -v Prop5Hold.lean ; echo $?
1
$ grep -nE "^(theorem|lemma|def|noncomputable def)" RBM3D/Propagator/Prop5Hold.lean
784:theorem prop5Decay_holds (d : ℕ) (Λ : ℝ) : Prop5Decay d Λ := by
1266:theorem prop8ZeroMode_holds (d : ℕ) (Λ κ : ℝ) : Prop8ZeroMode d Λ κ := by
```

## 5. Paper deltas
The Lean statements are the merged pins verbatim (§1). Every Lean/paper difference they carry is T2003a
(constants depend on `(d, Λ)`), T2003c (loss-free P8 instead of `≺`), T2003d (bulk `κ ≤ Im m`), T2003e (P5 for every
unit `m`), T2003f (periodic ℓ¹ `|a|`), all signed in DECISIONS §13. The prove report's (d) proposes no new candidate;
none is needed (the proof introduces no statement-level difference).

## 6. Observations (no effect on verdict)
- O1. Prove report (d) cites only T2003a; T2003c/d/e/f also apply to these two pins. Coverage exists (DECISIONS §13).
- O2. The P8 pin requires `κ ≤ Im m` also for `σ₁ ≠ σ₂`, where `Θ̊` does not depend on `m`; harmless (pin as signed).

## Verdict
| Target | Statement | Vacuity/hidden hyp. | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `prop5Decay_holds` | = pin | none | compiled, nondegenerate | pass / 3 std | covered | **PASS** |
| `prop8ZeroMode_holds` | = pin | none | compiled, nondegenerate | pass / 3 std | covered | **PASS** |

Ticket T2023: **PASS**. No dispatcher sign-off needed.
