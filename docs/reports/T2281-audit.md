Auditor model: claude-opus-5-5

# T2281 audit, round 1 (Tue Oct  6 11:18:10 UTC 2026)

Inputs: `docs/tickets/T2281.md`, `docs/tickets/T2281-amend-1.md` (scope reduced to the near part; far
targets and far vocabulary removed; step pinned in corrected form as `lwMomExp_near_step'`),
`docs/tickets/checks/T2281-check.lean`, `docs/reports/T2281-prove.md`, branch `t/T2281` at 350ef0c.
Audit worktree `RBM3D-wt/T2281-audit1` (detached at 350ef0c). Scratch: scratchpad `T2281/`.

Targets in scope after amendment 1: `lwMomExp_near : ∀ d, AnpDetNear d`; `lwMomExp_near_step'`;
instances `lwMomExp_inst_near` (+ `lwMomExp_inst_near_pt`), `lwMomExp_inst_step`.
Not in scope (amendment 1): `lwMomExp_far`, `lwMomExp_inst_far`, `farD`, `AnpDetFar*`, `NearStepShape`.

## 1. Diff scope, forbidden tokens, name clashes

```
$ git diff --name-only main...t/T2281
RBM3D/Graph/LWMomExp.lean
$ git log --oneline main..t/T2281
350ef0c T2281: LW-13a near part: lwMomExp_near, corrected step lwMomExp_near_step', instances
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Graph/LWMomExp.lean; echo $?
1
$ git grep -nE "lwMomExp_|AnpDetNear" main -- RBM3D | wc -l      # main at f3e7c74
       0
$ sed -n 6,12p RBM3D/Graph/LWMomExp.lean    # imports
import RBM3D.Graph.AnpKey6
import RBM3D.Evolution.Pins
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
```
New file only; `Test/Axioms.lean` untouched (owed `:162`, `:163` stay, as the ticket requires); no frozen
signature touched. Public names: pinned `AnpDetNearAt`, `AnpDetNear`; everything else `lwMomExp_*` or `private`
(48 private declarations).

## 2. Statement vs pin (script diff, check file section 2 vs file, prefix rename only)

```
$ python3 adiff.py   # whitespace-normalised def blocks; check-file names renamed valOnD->lwMomExp_valOnD, nearD->lwMomExp_nearD
valOnD        vs lwMomExp_valOnD : IDENTICAL
nearD         vs lwMomExp_nearD  : IDENTICAL
AnpDetNearAt  vs AnpDetNearAt    : IDENTICAL
AnpDetNear    vs AnpDetNear      : IDENTICAL
```
Elaboration against the check file's own definitions (check-file section 2 verbatim in `apin.lean`):
```
$ grep -n "^example" apin.lean
64:example : T2281Check.AnpDetNear 3 := lwMomExp_near 3
65:example : ∀ d, T2281Check.AnpDetNear d := lwMomExp_near
66:example : T2281Check.AnpDetNearAt 3 figAux := lwMomExp_inst_near
$ lake env lean apin.lean   (non-indented lines)
RBM.ekTTk_holds : ∀ (d n : ℕ), RBM.EKTTk d n
figAux_nested : figAux.IsNested ∧ figAux.NoGhost
'RBM.Graph.lwMomExp_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_near_step'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_near_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_inst_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_inst_near_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_inst_step' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Against the paper (`7_8:1650-1656`, `(adsuu_exp2)`): `𝐃_{≤ℓ}` with `∨` (both distances `≤ ℓ`) = `nearD` (`∧` of
the two `≤`); `[a_i] ≡ [a]`, `[b_i] ≡ [b]` = `fun _ => a`, `fun _ => b`; factors `(W^dη_t)^{-q}`,
`Ψ_t^{ord-p}`, `𝖳_t(|a-b|∧ℓ)^p` present with exponents `q`, `Γ.ordN - p`, `p`; `C` before `L, W, g, t, ℓ, Λ, ξ, a, b`
(`∃ C, … ∀ L …`); the regime `1-t ≥ g²/L²` carried as `g^2 ≤ L^2 (1-t)`, not dropped. Differences, all covered:
`≺` → explicit `C Λ^{2q}` and `η_t → 1-t`, `ℓ ≥ 1` (D36, `EKTTk`; and candidate `T2281e`), `|·|` → `zdistD`
(`T2281c`), edges `ξ ≤ 𝖳_t(·∧ℓ)` with `ξ` general (stronger than the paper's `𝖳_t`-edge graph).

`lwMomExp_near_step'` (file `:662`), against amendment 1 ("summing `α` visited by `k ≥ 2` passages via
`ekTTk_holds d k` on `ξ' = sfT(min(zdistD,ℓ))`, each passage replaced by `x_i y_i`; loops bounded by `T(0) ≤ Ψ`"):
```
theorem lwMomExp_near_step' (d N : ℕ) (hd : 3 ≤ d) : ∃ K : ℝ, 0 < K ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ a b : Zd d L,
      ∀ {p q : ℕ} (m : Fin p → List (NV p (q + 1))),
        ∑ i, ((m i).length + 1) ≤ N → (∃ i i', i ≠ i' ∧ Sum.inr 0 ∈ m i ∧ Sum.inr 0 ∈ m i') →
        lwMomExp_sysVal (lwMomExp_tau d L W g t ℓ) (lwMomExp_nearD d L a b ℓ) a b m ≤
          K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) * PsiT d L W g t ^ ((lwMomExp_occ m : ℤ) - 2) *
            lwMomExp_sysVal (lwMomExp_tau d L W g t ℓ) (lwMomExp_nearD d L a b ℓ) a b
              (lwMomExp_del m)
```
Definitions used (file `:56`, `:147`, `:241`, `:245`, `:521`): `lwMomExp_chain w x [m₁..mₙ] y = w x m₁ ⋯ w mₙ y`;
`sysVal = Σ_{ℓ ∈ D^{q}} Π_i chain(w, a, lab(m i), b)`; `del` = `filterMap` deleting `inr 0` and renumbering
(a passage `x α y` becomes the step `x y`); `occ` = number of occurrences of `inr 0`; `tau = sfT(min(zdistD,ℓ))`.
`k ≥ 2` is the hypothesis "`α` on two distinct paths" (`IsNested` (2)). `K` depends on `d, N` only, quantified
before `L…`. Form difference from the amendment: stated on path systems instead of `NGraph`; a passage `x α x`
(or step `α α`) is kept as a step of weight `sfT 0` (`≤ Ψ`, `sfT_zero_le_PsiT`) instead of being deleted with one
extra `Ψ`; the RHS is therefore at most the amendment's form, and the hypothesis set is weaker (no `IsNested`).
Covered by candidate `T2281d` (prove report (d)) and narrative 3(i). Not a special case.

## 3. Hidden hypotheses, vacuity, cycles

```
$ #print RBM.EKTTk   (apin.out, abridged to its premises)
3 ≤ d → 2 ≤ n → ∃ C, 0 < C ∧ ∀ (L) [NeZero L] (W g t), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ ↑L ^ 2 * (1 - t) →
  ∀ (ℓ Λ), 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ D a, (∀ α ∈ D, ↑(zdistD d L (a - α)) ≤ ℓ) → ∀ x y, …
```
- `ekTTk_holds : ∀ d n, EKTTk d n` is a merged theorem (standard axioms via the targets' axiom lines); no
  external hypothesis enters. `AnpDetNear`'s premises `NoGhost`, `IsNested` are the pinned graph conditions,
  satisfied by `figAux` (`figAux_nested`), so not vacuous. No structure field carries a hypothesis.
- Dependencies are merged modules (`Graph.AnpKey6`, `Evolution.Pins`); no cycle (the file imports neither
  `RBM3D` nor `LWPins`).

## 4. Compiled nonempty instances (file `:1036-1084`)

- `lwMomExp_inst_near : AnpDetNearAt 3 figAux := lwMomExp_near 3 le_rfl 2 2 figAux figAux_nested.2 figAux_nested.1`.
- `lwMomExp_inst_near_pt`: applies it at `L = 6, W = 2, g = 1/2, t = 1/2, ℓ = Λ = 2`, `ξ = lwMomExp_tau …`,
  `a = 0`, `b = Pi.single 0 1`; every premise discharged (`norm_num` for `0<W`, `0≤g`, `t<1`, `g²≤L²(1-t)`,
  `1≤ℓ`; `lwMomExp_inst_ell` for `ℓ ≤ Λ ℓ_t` via `one_le_ellT`; `tau_nonneg`/`tau_symm`; `le_rfl` for the edge
  bound) and proves `(nearD 3 6 0 e₀ 2).Nonempty` (`0 ∈ D`, `zdistD … = 1` by `decide`). `p = q = 2`, nonempty `D`.
- `lwMomExp_inst_step`: `lwMomExp_near_step' 3 6 le_rfl` at the same data, `m = lwMomExp_sysOf figAux`
  (`= [inr 0, inr 1]` on both paths), length bound by `decide`, two distinct paths through `inr 0` discharged;
  `k = 2`. Nondegenerate.
All compile (module build below). No `False` premise, `N = 0`, empty index or collapsed window.

## 5. Build and axioms (audit worktree)

```
$ lake build RBM3D.Graph.LWMomExp 2>&1 | grep -E "LWMomExp|error|Build completed"
Build completed successfully (3352 jobs).
exit 0
```
(no warning or error line mentions `LWMomExp`; axioms in section 2: only `propext`, `Classical.choice`,
`Quot.sound` for all six public theorems.) Full `lake build` is run by the hub at merge.

## 6. Paper-delta coverage

Prove report (d): `T2281a` (`7_8:1636-1640`, far; out of scope here), `T2281b` (`7_8:1602`, order),
`T2281c` (`zdistD` in `claim:TTk`/`nearD` vs `zdistInf` in `(eq:LW_moment_exp)`), `T2281d` (`7_8:1779-1784`,
self-loop passages; path-system step), `T2281e` (`7_8:1662`, `0 ≤ ℓ` vs `1 ≤ ℓ`). Explicit `Λ²`, `η_t ≍ 1-t`:
existing D36 (`docs/paper-deltas.md:299`). Every statement difference found in section 2 is covered.

## 7. Verdicts

| target | verdict |
|---|---|
| `lwMomExp_near : ∀ d, AnpDetNear d` | PASS |
| `lwMomExp_near_step'` (amendment 1 corrected step) | PASS |
| `lwMomExp_inst_near` / `lwMomExp_inst_near_pt` | PASS |
| `lwMomExp_inst_step` | PASS |
| far targets | not in scope (removed by amendment 1; back to the dispatcher) |

Observations (no effect on statement, instance, build, axioms or delta coverage):
- File is 1086 lines; amendment 1's size target is ≤ 1000 (stated in the prove report).
- The symmetry part of the `ξ` hypothesis is unused (kept as pinned).
- LW-13b still needs an edge bound in `zdistD` (`T2281c`, ticket (S2)); this is a consumer issue, not a defect here.

Overall: **PASS**. No dispatcher sign-off needed for the near part.
