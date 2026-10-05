Auditor model: claude-opus-5-5

# T2175 audit (round 1) — Mon Oct  5 05:58:47 UTC 2026

Branch `t/T2175` @ `cbe8c80`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2175-audit1` (detached).
Target: `RBM.Univ.gueP_map_unitary_conj` (endpoint) + port of `RBM2D/Universality/GUEInvariance.lean` @ `c9a24cf`.

## 1. Statement

Endpoint signature as elaborated (`lake env lean sig.lean`, `#check @RBM.Univ.gueP_map_unitary_conj`):
```
gueP_map_unitary_conj : ∀ (d L W : ℕ) [inst : NeZero L] [inst_1 : NeZero W],
  ∀ U ∈ Matrix.unitaryGroup (Gauss.Idx d L W) ℂ,
    MeasureTheory.Measure.map (fun ω => U * Gauss.Xmat d L W ω * star U) (gueP d L W) =
      MeasureTheory.Measure.map (Gauss.Xmat d L W) (gueP d L W)
@[reducible] def RBM.Gauss.Idx : ℕ → ℕ → ℕ → Type :=
fun d L W => Zd d (W * L)
def RBM.Univ.gueP : (d L W : ℕ) → [NeZero L] → [NeZero W] → MeasureTheory.Measure (Gauss.Ω d L W) :=
```
Matches the ticket: every `d L W`, `[NeZero L] [NeZero W]`, carrier `Idx d L W = Zd d (W*L)`, `gueP`/`Xmat` the merged
T2174/Gauss ones (not re-declared). No `3 ≤ d` (statement is dimension-free; none needed).

Script diff of all declaration headers (comments stripped; port normalised `d L W→L W`, `3 3 1→3 3`) vs source
(`git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Universality/GUEInvariance.lean`), `python3 hdr.py src.lean new.lean`:
```
source decls 103 port decls 104
--- src@c9a24cf
+++ port(normalised d L W->L W)
@@ -5 +5 @@
-private theorem GUE_card_idx : Fintype.card (Idx L W) = (W * L) ^ 2
+private theorem GUE_card_idx : Fintype.card (Idx L W) = (W * L) ^ d
@@ -79,0 +80 @@
+private theorem GUE_Xmat_apply (ω : Ω L W) (i j : Idx L W) : Xmat L W ω i j = Xentry L W ω i j
```
Only differences: the ticketed `N = (WL)^2 → (WL)^d`, and one added private rfl helper (RBM3D has no `Xmat_apply`).
All 103 source headers (incl. the public `gueP_map_unitary_conj` and the `GUEInvarianceCheck` names) kept verbatim.
Verdict on statement: PASS.

## 2. Vacuity / hidden hypotheses / cycles

- Hypotheses: only `U ∈ unitaryGroup` and the two `NeZero` instances; no structure-bundled hypothesis, no external hypothesis.
- Imports: `RBM3D.Universality.Pins` (merged, T2174 `f8ad4b4`) + Mathlib; `git diff --name-only main...t/T2175`:
```
RBM3D/Universality/GUEInvariance.lean
```
  so no merged module is modified; no cycle possible.
- Not vacuous: `gueP 3 3 1` is a probability measure (`isProbabilityMeasure_map_Xmat` compiles), so both sides are
  nonzero laws; `U` ranges over a nonempty group with a nonscalar member (below).
Verdict: PASS.

## 3. Compiled nonempty instance

In the same file (`GUEInvarianceCheck`, lines 1015–1071), at `d = 3, L = 3, W = 1` (`N = 27`):
```
theorem gueP_map_unitary_conj_one : ... := gueP_map_unitary_conj 3 3 1 1 (one_mem _)
theorem gueP_map_unitary_conj_phase : (gueP 3 3 1).map (fun ω =>
    phaseU (fun k => ((idxKey 3 3 1 k : ℕ) : ℝ)) * Xmat 3 3 1 ω *
      star (phaseU (fun k => ((idxKey 3 3 1 k : ℕ) : ℝ)))) = (gueP 3 3 1).map (Xmat 3 3 1) :=
  gueP_map_unitary_conj 3 3 1 _ (phaseU_mem _)
```
Independent recheck (`lake env lean sig.lean`, exit 0):
```
example : RBM.Univ.gueP_map_unitary_conj 3 3 1 1 (one_mem _) = RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_one := rfl
GUEInvarianceCheck.phaseU_not_scalar : ∀ (c : ℂ), (GUEInvarianceCheck.phaseU fun k => ↑(Gauss.idxKey 3 3 1 k)) ≠ c • 1
```
Unitarity discharged (`one_mem`, `phaseU_mem`); the phase instance is proved nonscalar; `NeZero 3`, `NeZero 1`
by instance. Nondegenerate (27 indices, no collapsed data). Verdict: PASS.

## 4. Build and axioms

`cd /Users/junyin/Lean_proof/RBM3D-wt/T2175-audit1 && lake build RBM3D.Universality.GUEInvariance` → `exit 0`.
Warnings/infos of this module only:
```
warning: RBM3D/Universality/GUEInvariance.lean:16:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Universality/GUEInvariance.lean:22:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Universality/GUEInvariance.lean:35:100: This line exceeds the 100 character limit, please shorten it!
info: RBM3D/Universality/GUEInvariance.lean:1073:0: 'RBM.Univ.gueP_map_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1074:0: 'RBM.Univ.GUEInvarianceCheck.phaseU_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1075:0: 'RBM.Univ.GUEInvarianceCheck.phaseU_not_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1076:0: 'RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1077:0: 'RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1078:0: 'RBM.Univ.GUEInvarianceCheck.isProbabilityMeasure_map_Xmat' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3345 jobs).
```
`grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Universality/GUEInvariance.lean | wc -l` → `0`.
Diff touches only the sole writable file (above); no frozen signature changed (no existing file touched).
Public-name clash on main (`git grep -n <name> main -- RBM3D RBM3D.lean | wc -l`):
```
gueP_map_unitary_conj: 0   GUEInvarianceCheck: 0   phaseU: 0   isProbabilityMeasure_map_Xmat: 0
```
Verdict: PASS.

## 5. Paper deltas

Lean statement = source statement with `Idx L W → Idx d L W` and `(WL)^2 → (WL)^d` (ticketed renaming); the GUE
law's unitary invariance is exact in the paper, no loss/window/energy. No Lean/paper statement difference; no
candidate needed. PASS.

## Observations (no effect on statement, instance, build, axioms or deltas)

- O1. Line 51 reads `variable (d d L W : ℕ) [NeZero L] [NeZero W]` (duplicated `d`). The elaborated endpoint
  signature above takes exactly one `d` (`∀ (d L W : ℕ)`), and the instance `gueP_map_unitary_conj 3 3 1 1 ...`
  applies with three naturals, so the shadowed binder is never included. Cosmetic; worth fixing in a later touch.
- O2. Three long-line lint warnings in the module docstring (lines 16, 22, 35).
- O3. RBM2D's file changed after `c9a24cf` (prove report diff-stat: 13+/99−); port follows `c9a24cf` as ticketed.

## Verdict

`gueP_map_unitary_conj` (and the file port): **PASS**. No dispatcher sign-off needed.
