Auditor model: claude-opus-5-5

# T2327 audit (round 1) — UN-32 `RBM3D/Universality/GUEPhase/Markov.lean`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2327-audit1`, detached at `t/T2327` = 85ac68f (merge-base with main 5c06348).
Started `date -u`: Thu Oct  8 10:23 UTC 2026. No `lake build` process was running at the start (`ps aux | grep -c "[l]ake build"` = 0), so H122/H101 (4) did not apply.

## 1. Build (audit worktree)
```
$ lake build RBM3D.Universality.GUEPhase.Markov ; echo exit $?
exit 0
$ ls -la -T .lake/build/lib/lean/RBM3D/Universality/GUEPhase/Markov.olean
-rw-r--r--@ 1 junyin  staff  4546392 Oct  8 03:23:11 2026 (local = 10:23:11 UTC, built in this worktree; absent from main's .lake/build)
$ lake build RBM3D.Universality.GUEPhase.Markov > build.log 2>&1; grep error build.log; grep "GUEPhase.Markov\|GUEPhase/Markov" build.log; tail -1 build.log
Build completed successfully (3743 jobs).
```
(no error lines; no warning lines from the new module on replay; the other warnings in the first run are from merged files.)

## 2. Statement vs pin (check-file equality, Lean-checked)
Script: copy `docs/tickets/checks/T2327-check.lean`, add `import RBM3D.Universality.GUEPhase.Markov`, comment out `#check`s, replace the final `example : Prop` with:
```
92:example {d : ℕ} (sz : Sizes d) : RBM.Univ.GUEPhase.T2327Check.T2327_gueCondExp_freeze sz := RBM.Univ.GUEPhase.gueCondExp_freeze sz
93:example {d : ℕ} (sz : Sizes d) : RBM.Univ.GUEPhase.T2327Check.T2327_gueHasCondSubgaussianMGF_of_frozen sz := RBM.Univ.GUEPhase.gueHasCondSubgaussianMGF_of_frozen sz
94:example {d : ℕ} (sz : Sizes d) : RBM.Univ.GUEPhase.T2327Check.T2327_gueMap_lin_Xmat sz := RBM.Univ.GUEPhase.gueMap_lin_Xmat sz
95:example {d : ℕ} (sz : Sizes d) : RBM.Univ.GUEPhase.T2327Check.T2327_gueHasCondSubgaussianMGF_linear sz := RBM.Univ.GUEPhase.gueHasCondSubgaussianMGF_linear sz
96:example {d : ℕ} (sz : Sizes d) : RBM.Univ.GUEPhase.T2327Check.T2327_gue_highProb_incr_le sz := RBM.Univ.GUEPhase.gue_highProb_incr_le sz
97:example {d : ℕ} (sz : Sizes d) (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : RBM.Univ.GUEPhase.T2327Check.vGue sz n A = RBM.Univ.GUEPhase.vGue sz n A := rfl
$ lake env lean eq.lean ; echo exit $?
exit 0     (axiom lines in section 3; no errors)
```
- The five theorems are exactly the check's pinned propositions (with `β : Type*` in the file vs `β : Type` in the check: the file is more general, allowed by the ticket); `vGue` agrees with the check's verbatim definition by `rfl` (the prover's whitespace-normalized text comparison, report (b5)(a), also gives EQUAL).
- Quantifier order and parameters match the pin: `d`, `sz` fixed; `n0` before `HighProbAt` (`∀ D > 0, ∀ᶠ n`); grid range `1 ≤ k ≤ gueGridK sz n0 n`; all index pairs `i j : Idx d (sz.L n) (sz.W n)`; threshold `sz.size n`; scale `sz.size`.

## 3. Axioms (same scratch file)
```
'RBM.Univ.GUEPhase.gueCondExp_freeze' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueHasCondSubgaussianMGF_of_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueMap_lin_Xmat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueHasCondSubgaussianMGF_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gue_highProb_incr_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.vGue' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.vGue_one_pos_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gueMap_lin_Xmat_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gueCondExp_freeze_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gueHasCondSubgaussianMGF_of_frozen_sz0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gueHasCondSubgaussianMGF_linear_sz0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gue_highProb_incr_le_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. Hygiene, scope, imports, clashes
```
$ git diff --name-status main...t/T2327
A	RBM3D/Universality/GUEPhase/Markov.lean          (1 file changed, 1135 insertions(+); the sole writable file)
$ git show t/T2327:RBM3D/Universality/GUEPhase/Markov.lean | grep -nwE "sorry|admit|native_decide|axiom" | wc -l
       0
$ ... | grep -n "^import"
6:import RBM3D.Universality.GUEPhase.Grid
7:import RBM3D.Path.Markov
8:import Mathlib.Probability.Moments.SubGaussian
$ git grep -nw <name> main -- 'RBM3D/*.lean' | grep -v /Probe/ | wc -l   (current main 9cd356f)
gueCondExp_freeze 0 / gueHasCondSubgaussianMGF_of_frozen 0 / vGue 0 / gueMap_lin_Xmat 0
gueHasCondSubgaussianMGF_linear 0 / gue_highProb_incr_le 0 / MarkovInst 0
$ git diff --stat 5c06348 main -- RBM3D/Universality/GUEPhase/Grid.lean RBM3D/Path/Markov.lean
(empty: the dependencies did not change on main since the branch point)
```
Imports are exactly the ticket's three; no merged file is touched; no frozen signature changed. Unpinned helpers are `private` with the prefix `Markov_`, or public in `MarkovInst` (`markovInstOne/Coord/F`, instance theorems).

## 5. Hidden hypotheses, vacuity, cycles
- No new `structure`/`class`; the hypotheses are all in the theorem signatures (section 2). The only structure is the merged `Sizes d`.
- Dependencies: merged modules only (`Grid`, `Path/Markov`, Mathlib). No cycle (new leaf module).
- `gue_highProb_incr_le` hypothesis `Tendsto (fun n => sz.size n) atTop atTop`: deterministic, discharged at `sz0` by `sz0_size_tendsto_nat := tendsto_natCast_atTop_iff.1 sz0_tendsto` (merged). Limit check: `sz0.size n = ((2(n+1))^5 · 4(n+1))^3 → ∞`.
- `StandardBorelSpace β`, measurability, integrability, sub-Gaussianity hypotheses: all discharged at `β = ℝ` in the instances (section 6). No pinned external gate is left open.

## 6. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.MarkovInst`, same file, built above)
```
#print RBM.Gauss.SizesInst.sz0
def RBM.Gauss.SizesInst.sz0 : RBM.Gauss.Sizes 3 :=
{ L := fun n => 4 * (n + 1), W := fun n => (2 * (n + 1)) ^ 5, lam := fun n => ((2 * (↑n + 1)) ^ 6)⁻¹, ... }
```
| target | instance | data | deterministic hypotheses |
|---|---|---|---|
| `gueCondExp_freeze` | `gueCondExp_freeze_sz0 (k)` | `d=3`, `sz0`, `β=ℝ`, `Y ω = ω k c₀` (non-constant), `F y x = cos y · Re tr(seqXmat sz0 0 x)` | `hY` (`Markov_measurable_eval_filt`), `hF`, `hInt` (`markovInst_integrable`) proved |
| `gueHasCondSubgaussianMGF_of_frozen` | `..._of_frozen_sz0 (k)` | same, `c = vGue sz0 0 1` | `hsub : ∀ y, HasSubgaussianMGF (F y) c` proved (`markovInstF_subgaussian`) |
| `gueMap_lin_Xmat` | `gueMap_lin_Xmat_sz0 (n)` | `A = 1`, every `n`; conjoined `0 < vGue sz0 n 1` | none (no hypotheses); law nondegenerate |
| `gueHasCondSubgaussianMGF_linear` | `..._linear_sz0 (k)` | `n=0`, `s=1`, `A ≡ 1`, `E = {ω k c₀ ≤ 0}` (nontrivial), `c = vGue sz0 0 1 > 0` | `hA` (`measurable_const`), `hE`, `hbound` (`by simp`, equality) |
| `gue_highProb_incr_le` | `gue_highProb_incr_le_sz0` | `n0 = 1` (ticket) | `hsize` discharged (section 5) |

No `N = 0` (size index 0 has `N = (32·4)^3 = 2097152`), no empty index type, no `False` premise; `gueGridK` is a set bound inside the event, not a constructed witness. The `gueMap_lin_Xmat` instance is at `A = 1` as the ticket requires.

## 7. Paper deltas
- No paper statement is pinned (ticket: Gaussian tail and independence only; the paper defers to [YY_25, Thm 2.6] at `1_2_Intro_model_result.tex:566-570`). The Lean-specific choices (hard-coded grid range `(N+1)^(32 n₀+64)`, threshold `N`, extra hypothesis `Tendsto sz.size`) are proposed as candidate **T2327a** in the prove report (d); the `Type*` generalisation as **T2327b**. Coverage complete.

## 8. Observations (no RETURN)
- Prove report (a) says "`vGue = N = 2097152`" at `n = 0`; only `0 < vGue` is proved in Lean. The report's own (a′) records this.
- The prove report states the ticket's `RBM.Path.hfun` re-derivation was unnecessary (source uses a local `have`); this changes no target statement.

## Verdict
| target | verdict |
|---|---|
| `vGue` (def, pinned verbatim) | PASS |
| `gueCondExp_freeze` | PASS |
| `gueHasCondSubgaussianMGF_of_frozen` | PASS |
| `gueMap_lin_Xmat` | PASS |
| `gueHasCondSubgaussianMGF_linear` | PASS |
| `gue_highProb_incr_le` | PASS |

Ticket T2327: **PASS**. No dispatcher sign-off needed.
