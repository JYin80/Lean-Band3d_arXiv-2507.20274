Auditor model: claude-opus-5-5

# T2150 audit (round 1) — S5-12 `Induction/NewKLKL`, target `stNewKLKL_holds`
Written: Sun Oct  4 18:23:08 UTC 2026. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2150-audit1` (detached at t/T2150 = ef46fb0).

## 1. Diff scope (sole writable files)
```
$ git diff --stat main...t/T2150
 RBM3D/Induction/NewKLKL.lean | 956 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |   1 -
$ git diff main...t/T2150 -- RBM3D/Test/Axioms.lean   (registry: one owed line removed)
-   `RBM.Gauss.Sizes.STNewKLKL, -- `lem:newKLK` sharp at `ℓ = L` (paper-delta T2134a); S5-01 (T2138, DECISIONS §40: owed)
$ git diff --stat main...t/T2150 -- RBM3D/Induction/Step5Pins.lean RBM3D/Induction/NewKLK.lean
(empty: pin file and merged NewKLK untouched)
```
New file imports only `RBM3D.Induction.NewKLK`, `RBM3D.Induction.Step5Pins` (not `RBM3D`).

## 2. Statement against the pin
```
$ lake env lean Ax.lean   (#check @stNewKLKL_holds)
stNewKLKL_holds : ∀ (d : ℕ), STNewKLKL d
```
Ticket target: `stNewKLKL_holds (d : ℕ) : STNewKLKL d`, "the merged statement unchanged" — identical. `STNewKLKL` is the
merged pin (`Step5Pins.lean:245`, c8e4f17, not modified): `3 ≤ d → ∀ κ 𝔡, 0<κ → 0<𝔡 → ∃ C δ₀, 0<C ∧ 0<δ₀ ∧ STNewKLKLAt d κ 𝔡 C δ₀`,
with `STNewKLKLAt` quantifying `∀ sz n E u D H` after the constants (paper order: constants before sizes). RHS
`C/(1-u) * (Ĵ² * STprof … + Ĵ * (W^d)⁻¹ * W^(-D))`: no term linear in `Ĵ` against the profile, as the ticket requires.
Constants in the proof: `C = 10 + 2^(d-2) e C_T` (depends on `d` only), `δ₀ = κ/2` (`newKLKL_at`, line 732) — within
"depending on d, κ, 𝔡 only".  PASS.

## 3. Vacuity, hidden hypotheses, cycles
- `stNewKLKL_holds` has no hypotheses beyond the pin's own; no structure carrying a Prop field is introduced
  (`grep structure/class` in the new file: none; `newKLKLsz31 : Sizes 3` is data only).
- Only external input used: `ekPropTInf_holds d hd` (`(TTT2)`), a merged *theorem*
```
$ grep -rn "theorem ekPropTInf_holds" RBM3D
RBM3D/Evolution/PropTInf.lean:534:theorem ekPropTInf_holds (d : ℕ) : EKPropTInf d := by
$ git log --oneline -1 main -- RBM3D/Evolution/PropTInf.lean
a84c579 T2075: merge ST2-06b (TTT2) of lem:propT for zdistInf (Evolution/PropTInf)
```
- The pin's premise `‖G_u − M‖_max ≤ δ₀` is the merged pin's (same as `STNewKLK`); it is discharged nontrivially in the
  instances (`G_u − M = i u/(1-u) I ≠ 0`, §4).  No cycle: the file imports only merged modules.  PASS.

## 4. Compiled nonempty instances (same file)
```
$ grep -n "^example\|^private def newKLKLsz31" RBM3D/Induction/NewKLKL.lean
893:example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
920:private def newKLKLsz31 : Sizes 3 where
930:example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
```
- l.893: `stNewKLKL_holds 3` at merged `sz0`, `n = 0` (`L = 4, W = 32, lam = 1/64`), `κ = 𝔡 = 1/10`, `E = 0`, `D = 1`,
  `H = 0`, `u = δ₀/(1+δ₀) ∈ (0,1)`; every hypothesis of `STNewKLKLAt` discharged (`lam` bounds by `norm_num`,
  `|E| ≤ 2-κ`, `0 ≤ u < 1`, `0 ≤ D`, `Matrix.isHermitian_zero`, `‖G−M‖ ≤ δ₀` via `newKLKL_STGMM_zero`), for all `σ, a`.
- l.930: same at `d = 3, L = 3, W = 1` (`N = 27`), `lam = 1`, `κ = 𝔡 = 1`, `H = 0` — the ticket's second instance.
- No `N = 0`, no empty index, no `False` premise, `u > 0` so `G_u ≠ M`.  Both compile (build §5).  PASS.

## 5. Build, axioms, hygiene
```
$ lake build RBM3D.Induction.NewKLKL
⚠ [3775/3775] Built RBM3D.Induction.NewKLKL (6.5s)
warning: RBM3D/Induction/NewKLKL.lean:12:100: This line exceeds the 100 character limit, please shorten it!
  (… 12 further longLine warnings, lines 13–34 of the module docstring; no other warnings in NewKLKL.lean)
Build completed successfully (3775 jobs).
$ grep -c error build.txt
0
$ lake env lean Ax.lean
'RBM.Gauss.Sizes.stNewKLKL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/NewKLKL.lean; echo grep-exit $?
grep-exit 1
$ git grep -n "stNewKLKL_holds" main -- RBM3D        (name clash: none)
$ grep -nE "^(theorem|lemma|def|abbrev|instance)" RBM3D/Induction/NewKLKL.lean   (public names)
836:theorem stNewKLKL_holds (d : ℕ) : STNewKLKL d := by
```
All helpers are `private` with prefix `newKLKL_` (§3 (E)).

Registry pre-check (scratch root = all `import` lines of `RBM3D.lean` + `import RBM3D.Induction.NewKLKL` + `#assert_rbm_axioms`):
```
$ lake env lean Reg.lean; echo exit $?
exit 0
axiom audit: 4639 theorems, 1640 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 86 (borrowed 0, owed 66, structural 20).
```
(Without the root import, `lake build RBM3D` in this worktree reports `1 premise(s) that no theorem … proves are in none of
… owedProps …` — expected, since the hub adds `import RBM3D.Induction.NewKLKL` at merge; the hub's full build is decisive.)

## 6. Paper deltas
- Statement difference (sharp form at `ℓ = L` vs printed `(juwo=Lklk)`) is already `docs/paper-deltas.md` D315 (`T2134a`):
```
$ grep -n "D315" docs/paper-deltas.md
1273:- **D315（T2134a）**：`lem:newKLK` 在 `ℓ = L` 取锐形式 `C/(1−u)(Ĵ² W^{-d}𝒯̃^L + Ĵ W^{-d-D})`（`STNewKLKL`）…
```
- Report (d) proposes `T2150a` (pointwise near/far split replacing `3_5:612-616`, route only) and `T2150b` (explicit
  constants; weak law as the pin's hypothesis `‖G_u−M‖_max ≤ δ₀`).  Coverage complete.  PASS.

## Observations (no effect on verdict)
- 13 `longLine` linter warnings in the module docstring (`set_option linter.style.longLine false` is placed after it).

## Verdict
| Target | Verdict |
|---|---|
| `stNewKLKL_holds (d : ℕ) : STNewKLKL d` | **PASS** |

Ticket T2150: **PASS**.  No dispatcher sign-off needed.
