Auditor model: claude-opus-5-5

# T2083 (ST2-21) audit, round 1. Sat Oct  3 23:08:42 UTC 2026

Branch `t/T2083` at `0ad5adb` (main `7f9bfa1`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2083-audit1` (detached).
Targets: `condExp_loop_step`, `condExp_loop_drift` (+ `pathH_succ`) in `RBM3D/Path/LoopStep.lean`; pins `KpmODE`, `LoopGenN2`, `HierarchyN2` and theorems `kpmODE`, `loopGenN2`, `hierarchyN2` in `RBM3D/Path/DriftAlgebra.lean`.
The check file `docs/tickets/checks/T2083-check.lean` pins no statement text (only `#check` of `genMat`, `envConst`, `OneStepEnvelope`, `Sizes.Lloop`), so I checked the statements against RBM2D `c9a24cf` and the paper.

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Path.LoopStep RBM3D.Path.DriftAlgebra ; echo rc=$?   (error/warning lines of the two new files, then tail)
rc=0
warning: RBM3D/Path/DriftAlgebra.lean:27:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3749 jobs).
$ lake env lean scratchpad/T2083/audit.lean      (#print axioms)
'RBM.Path.pathH_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.condExp_loop_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.condExp_loop_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.kpmODE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.loopGenN2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.hierarchyN2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LoopStep_check_step_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LoopStep_check_drift_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.DriftAlgebra_check_kpmODE_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.DriftAlgebra_check_loopGenN2_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.DriftAlgebra_check_hierarchyN2_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --name-status main...HEAD
A	RBM3D/Path/DriftAlgebra.lean
A	RBM3D/Path/LoopStep.lean
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " <both files>; echo grep_rc=$?
grep_rc=1
$ name-clash grep "(theorem|def|lemma|abbrev) <name>\b" over RBM3D
pathH_succ / condExp_loop_step / condExp_loop_drift: RBM3D/Path/LoopStep.lean only
KpmODE / LoopGenN2 / HierarchyN2 / kpmODE / loopGenN2 / hierarchyN2: RBM3D/Path/DriftAlgebra.lean only
```
Only the two new sole-writable files are touched; no existing file is changed, so no frozen signature is touched. `RBM3D/Test/Axioms.lean` is unchanged: no new premise, and every pin is proved.

## 1. Statements

**LoopStep.** The statement text (LoopStep.lean:48, :206, :310) against RBM2D `c9a24cf:RBM2D/Path/LoopStep.lean:48, :205, :307`:
the hypotheses and their order are the same (`|E|<2`, `I.WF`, `u_{k+1}<1`; for the drift also `0 ≤ s n`, `s n ≤ t n`, `K n ≠ 0`, `k < K n`).
Renames: `Z2 → Zd d`, `gloop → loopL d`, `spectralZ → zt`, `P (d.L n) (d.W n) → PF d (sz.L n) (sz.W n) (sz.lam n)`, `genMat E → genMat d L W (sz.lam n) E`, `envConst L W → envConst d L W`.
No hypothesis was added and none was dropped. The right side of the drift is exactly the merged pin, applied at `M = pathH k ω`:
```
$ grep -n "^def OneStepEnvelope" -A8 RBM3D/Path/OneStep.lean
85:def OneStepEnvelope : Prop :=
86-  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E : ℝ), |E| < 2 → ∀ (I : Loop.LoopIdx (Zd d L)),
87-    I.WF → ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
...
91-            loopL d L W (blockMat d L W M) (zt E u) I - (Δ : ℂ) * genMat d L W g E u M I‖ ≤
92-          envConst d L W E I.length (u + Δ) * Δ ^ ((3 : ℝ) / 2)
$ #check @RBM.Path.oneStepEnvelope
oneStepEnvelope : OneStepEnvelope
```
`envConst` (OneStep.lean:79) has `N = ((W*L)^d)` explicitly, so it carries no hidden `d = 2` exponent. The window: `condExp_loop_step` needs only `u_{k+1} < 1`. The drift theorem derives `0 ≤ Δ` from `s ≤ t`, and `0 ≤ u_k` from `0 ≤ s` (DECISIONS §29).

**DriftAlgebra pins** (DriftAlgebra.lean:51, :62, :75), against RBM2D `DriftAlgebra.lean:55-69`:
- The coefficient changes from `W^2` to `W^d`, and `Z2 L` becomes `Zd d L`.
- `Kpm` becomes `STKloop ![true,false]`. `LLpair` becomes the explicit `W^d Σ STLM S STLM`. `EGt`, `ELKLK`, `lkMat` and `thetaGen` become `STEGtM`, `STELKLKM`, `STLKM` and `STthetaOp` (merged `Induction/{Defs,Step2Defs}.lean`).
- The definitions used are the paper's objects. `STEGtM` is (`def_EwtG`) at n=2, `STELKLKM` is (`def_ELKLK`) at n=2, and `STthetaOp` is `DefTHUST` at n=2 with `M = m(σ₁)m(σ₂)`.
- The `W^d` coefficient matches the paper:
```
$ grep -n "label{pro_dyncalK}" -A3 paper/tex/1_2_Intro_model_result.tex
990: \begin{align}\label{pro_dyncalK}
993:       W^d \sum_{1\le k < l \le n} \sum_{a, b} \left( \cutL^{(a)}_{k, l} \circ \mathcal{K}^{(n)}_{t, \bsig, \ba} \right) S^{(\sB)}_{ab} ...
$ grep -n "label{eq:mainStoflow}" -A2 ...
951:\begin{align}\label{eq:mainStoflow}
953:   W^{d} \sum_{1 \le k < l \le n} \sum_{a, b} \left( {\cutL}^{(a)}_{k, l} \circ \mathcal{L}^{(n)} ... \right) S^{(\sB)}_{ab} ( {\cutR}^{(b)}_{k, l} \circ ...) \dd t,
```
At n=2, `Σ_{a,b} 𝓛_{(a,a₂)} S_{ab} 𝓛_{(a₁,b)}` is the Lean `Σ_{b₁,b₂} 𝓛_{(a₁,b₁)} S_{b₁b₂} 𝓛_{(b₂,a₂)}` after renaming and using `S` symmetric. This is a shape difference only, covered by T2083b.

**Quantifier shape.** RBM2D has `∀ L W [NeZero L] [NeZero W] E, 3 ≤ L → …`, while RBM3D has `∀ sz : Sizes d, ∀ n, …`.
`Sizes` has only the fields `L W lam`, `three_le_L : ∀ n, 3 ≤ L n` and `W_pos : ∀ n, 0 < W n` (`Defs/Sizes.lean:138-146`). So `∀ sz n` covers every `(L, W, g)` with `3 ≤ L`, `0 < W` and any real `g`, through the constant sequence. This is not a weakening. Compiled check:
```
example (d L W : ℕ) (g : ℝ) (hL : 3 ≤ L) (hW : 0 < W) :
    let sz : Sizes d := ⟨fun _ => L, fun _ => W, fun _ => g, fun _ => hL, fun _ => hW⟩
    sz.L 0 = L ∧ sz.W 0 = W ∧ sz.lam 0 = g ∧ LoopGenN2 d ∧ HierarchyN2 d ∧ KpmODE d :=
  ⟨rfl, rfl, rfl, loopGenN2 d, hierarchyN2 d, kpmODE d⟩
$ lake env lean scratchpad/T2083/audit.lean ; echo rc=$?
rc=0          (no error lines)
```
The hypotheses `|E| < 2` and `0 ≤ u < 1` are RBM2D's; `3 ≤ L` moved into `sz`. The ticket asks ST2-28a to keep the shape of `HierarchyN2`. It is now fixed as `∀ sz n` with the merged `ST*` vocabulary, recorded in T2083a.

Result:
- The statements are faithful ports with the `d`-dimensional exponents.
- The targets are the n=2, σ=(+,-) pins that the ticket and portmap P.1 rows 15 and 29 name.
- General `n` is ST2-28a. The report flags it as a special case in T2083a.

## 2. Vacuity, hidden hypotheses, cycles

- `kpmODE`, `loopGenN2`, `hierarchyN2` are unconditional theorems `(d : ℕ) → Pin d`.
- `condExp_loop_step` and `condExp_loop_drift` have only deterministic hypotheses. No `Prop` structure field is assumed: `Sizes` carries only `3 ≤ L` and `0 < W`.
- The dependencies are merged modules: `OneStep` (T2072), `Markov`, `Induction/Step2Defs`, `Propagator/*` and `Loop/KLTree`. Neither file is imported by an upstream module (both are new). There is no external hypothesis, so no limit check is needed.
- `_hK` and `_hk` are unused. This is as in RBM2D and is disclosed in T2083c. It does not make the statement vacuous: the conclusion is the full envelope bound.

## 3. Compiled nonempty instances

```
$ #print RBM.Gauss.SizesInst.sz0
def RBM.Gauss.SizesInst.sz0 : Sizes 3 :=
{ L := fun n => 4 * (n + 1), W := fun n => (2 * (n + 1)) ^ 5, lam := fun n => ((2 * (↑n + 1)) ^ 6)⁻¹, ... }
```
At `n = 0` this gives d=3, L=4, W=32, λ=1/64. The table lists each named check, the theorem it applies, and how each hypothesis is discharged.

| check (file:line) | applies | hypotheses discharged at the data |
|---|---|---|
| `LoopStep_check_step_sz0` (LoopStep:375) | `condExp_loop_step` | s=1/10, t=1/2, K=4 (Δ=1/10), k=0, E=0. `|E|<2` by `norm_num`. `I.WF` by `rfl` (loop `(+,-;0,1)`). `u_1 = 1/5 < 1` (`LoopStep_inst_gridTime`) |
| `LoopStep_check_drift_sz0` (LoopStep:393) | `condExp_loop_drift` | the same data, plus `0 ≤ s`, `s ≤ t`, `K ≠ 0`, `0 < K` by `norm_num` |
| example (LoopStep:417) | `pathH_succ` | `sz0`, k=0 |
| `DriftAlgebra_check_kpmODE_sz0` (:713) | `kpmODE 3` | E=0, u=1/2, a=0, b=1 |
| `DriftAlgebra_check_loopGenN2_sz0` (:723) | `loopGenN2 3` | E=0, u=1/2, M=1 (`Matrix.isHermitian_one`), labels 0, 1 |
| `DriftAlgebra_check_hierarchyN2_sz0` (:740) | `hierarchyN2 3` | as above |
| `*_check_labels_sz0` | — | `(0 : Zd 3 4) ≠ 1` (by `decide` on a coordinate) |

No instance is degenerate: N=(128)^3, the window is open, the loop is nonempty with distinct labels, no premise is `False`, and no hypothesis is left open. All checks compile (the build above passes) and use only the standard axioms (list above).

## 5. Paper deltas

The prove report §(d) proposes three candidates:
- **T2083a**: the special case (n=2, σ=(+,-)) and the `∀ sz n` shape at `g = sz.lam n`. The equivalence with `∀ L W g` is shown in §1 above.
- **T2083b**: the merged `ST*` vocabulary and the index order of `STELKLKM`.
- **T2083c**: the bound is the `envConst·Δ^{3/2}` envelope, not RBM1D's `loopDrift`/Lip terms, and `_hK`/`_hk` are unused.

The paper's continuous-time SDE becomes a discrete grid step, the design of the merged MD layer (T2072 and its predecessors). This ticket adds no new difference. Every Lean/paper difference I found is covered by one of these candidates.

## Observations (no verdict effect)

- O1: The prove report §(b) says `lake env lean` of both files gives "no output = no error, no warning". `lake build` does print one style warning, `DriftAlgebra.lean:27:100` (a long line in the module docstring, before `set_option linter.style.longLine false`). The project's linter options apply under `lake build` and not under `lake env lean`, so both outputs are consistent. This is cosmetic.
- O2: The `*_check_*_sz0` theorems are public but carry the file-stem prefix, so they satisfy CLAUDE.md §3 (E).
- O3: The preflight numeric check (a)(ii) was done at d=3, L=3, W=2, Δ=10⁻³ as the ticket asks. It reports the step identity and that `W^d` is preferred over `W^2`. I did not rerun the script; the Lean proofs carry the statements.

## Verdicts

| target | verdict |
|---|---|
| `condExp_loop_step` | PASS |
| `condExp_loop_drift` | PASS |
| `pathH_succ` (helper, public) | PASS |
| `KpmODE` / `kpmODE` | PASS |
| `LoopGenN2` / `loopGenN2` | PASS |
| `HierarchyN2` / `hierarchyN2` | PASS |

**Overall: PASS.** No dispatcher sign-off is needed. The hub runs the full `lake build` at merge.
