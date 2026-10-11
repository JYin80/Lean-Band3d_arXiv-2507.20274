Auditor model: claude-opus-5-5
# T2410 audit (round 1) — Sun Oct 11 08:44:58 UTC 2026
Branch t/T2410 at b763c11; audit worktree /Users/junyin/Lean_proof/RBM3D-wt/T2410-audit1 (detached). Stop line: `wc -l RBM3D/Graph/BAGGOp.lean` = 1852 of 2000.

## 1. Diff scope
```
$ git diff --name-only main...t/T2410
RBM3D.lean
RBM3D/Graph/BAGGOp.lean
$ git diff main...t/T2410 -- RBM3D.lean   (one line, after the last import, before #assert_rbm_axioms)
 import RBM3D.BA.GreenLocal
+import RBM3D.Graph.BAGGOp
```
Only the sole writable files; no frozen signature touched (no existing file other than RBM3D.lean changed).

## 2. Statements against the pins (whitespace-normalised script diff, pin = `git show 4c1de4c:RBM3D/Probe/T2395Pins.lean`)
```
$ diff <(sed -n '129,148p' probe | norm) <(sed -n '73,92p' BAGGOp.lean | norm) && echo ...
gg2/gg4 (probe 129-148 vs BAGGOp 73-92): identical
$ diff <(sed -n '244,251p' probe | norm) <(sed -n '838,845p' BAGGOp.lean | norm) && echo ...
BAexpFrameE (probe 244-251 vs BAGGOp 838-845): identical
```
(Wider-range diffs differ only by docstring/blank lines.)
- **T1 `BAGraph.gg2`, `BAGraph.gg4`**: verbatim. Correctness against (B.20)+D402 is enforced by T2 being proved from merged `baGGGamma_holds` (`BAGGOp.lean:658`). PASS.
- **T2 `baExpFrame_gg`** (`:785`): `∀ L W [NeZero L] [NeZero W], 3 ≤ L → ∀ g0 Em t m, BASelf d L g0 Em m → 0 ≤ t → t < 1 → ∀ Γ ℓe, ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, p.1.σ → p.1.circ → q.1.σ → q.1.circ → p.1.src = q.1.dst → ∫ Γ.val = ∫ baSum gg2 + baSum gg4 ∂(PF d L W 0)`. It is used verbatim as the second conjunct of the pinned `BAexpFrameE` in `baExpFrameE_holds` (`:848-850`), so it has exactly the pinned hypotheses and quantifier order (Lean checks this). No distinctness of x, y, y'; no smallness of g, ‖M − m₀I‖, no `(Cλ)^{|a−b|}` (C1/L5). PASS.
- **T3 `BAexpFrameE`, `baExpFrameE_holds : ∀ d, BAexpFrameE d`**: definition verbatim (above); proof is `⟨baExpFrame_lw …, baExpFrame_gg …⟩` (`:848-850`), `baExpFrame_lw` merged (T2407). PASS.
- **T4 counters/order** (`:1621-1726`), same shape as merged `lw_counters`/`lw_raw`/`lw_scalingOrderG`/`lw_mono` (`BAWeightOp.lean:1680,1708,1731,1815`), hypotheses only `p ∈ lwSplit Γ.solid`, `q ∈ lwSplit p.2` (+`Γ.Normal` for ordG) — weaker than the lw versions:
  - `gg_counters`: A1 `(n_S−2, n_W+1, n_A−κ, n_M≤)`; A2,A3 `(n_S−1, n_W+1, n_A, n_M≤)`; A4,A5,AD `counters = (+1,+1,+1, n_M)`; every gg4 term `(+1,+2,+2, n_M)`.
  - `gg_raw`: `ord A1 = ord Γ + 2κ` (`κ = BAGGOp_kappa Γ q.1.src p.1.dst ∈ {0,1}`), every term of `(gg2).tail` and of `gg4` has `ord T° = ord Γ + 1`. This states exactly which term keeps the order (A1 iff κ = 0) and which gain, as the ticket asks (T2387 `baGGT1.scalingOrder = baGGLhs.scalingOrder` = instance `A1_keeps`). A1 is stated without `BAWeightOp_circ`; `BAWeightOp_circ_counters` (`BAWeightOp.lean:1652`, counters unchanged by circling) makes this the same number.
  - `gg_scalingOrderG`: `ord Γ ≤ ordG T` for all terms, Γ normal (non-strict; delta T2410a/T2398b).
  - `gg_mono`: `BAGGOp_Mono Γ T` = `n_M(T°) ≤ n_M(Γ) ∧ n_A−n_W(T°) ≤ n_A−n_W(Γ) ∧ nExt(T°) ≤ nExt(Γ)`; `BAGGOp_nExt` body equals probe `BAGraph.nExt` (probe :33) — these are the three counter conjuncts of the pinned `BAstepMono` (probe :272-273). PASS.

## 3. Hidden hypotheses, vacuity, cycles
- No structure carries a hypothesis. New public defs `BAGGOp_kappa`, `BAGGOp_nExt`, `BAGGOp_Mono`, `BAGGOp_A1..BD` are data/Prop definitions used in conclusions only (stem-prefixed, §3(E)).
- Dependencies: `baGGGamma_holds` (merged T2409), `baExpFrame_lw`, `BAWeightOp_*`/`BAExpandWOrd_*` private lemmas via `open private` (merged T2407 and earlier). No external hypothesis, so no limit check needed. No cycle (new file, imported by nothing).
- Name clashes on main (`grep -rnE "^(theorem|def|…) +<name>\b" RBM3D`): 0 for each of gg_counters, gg_raw, gg_scalingOrderG, gg_mono, baExpFrame_gg, BAexpFrameE, baExpFrameE_holds, BAGraph.gg2, BAGraph.gg4, BAGGOp_kappa, BAGGOp_nExt, BAGGOp_Mono, BAGGOpInst.

## 4. Compiled nonempty instances (`RBM.Graph.BAGGOpInst`, `:1737-1848`)
Data: d = 3, L = 3, W = 1 (27 sites), g0 = 0, E = 0, t = 1/2, m = i, `BASelf` discharged by merged `BAExpandInst.baSelf_zero`; `3 ≤ L`, `0 ≤ t`, `t < 1` by `norm_num`; flags by `rfl`; `hp*`, `hq*` by `simp [lwSplit]`, `hN*` by `decide`.
- T3: `(baExpFrameE_holds 3 3 1 … baGGLhs _).2 p0 hp0 q0 hq0 rfl rfl rfl rfl rfl` (`:1827`), ℓe = (e₁, e₀).
- T2: `baExpFrame_gg 3 3 1 … baGG3 _ p3 hp3 q3 hq3 rfl rfl rfl rfl rfl` (`:1838`), q3.2 ≠ [] so derivative terms AD, BD occur (`lists_baGG3`: lengths 6 and 3).
- T1: `lists_baGGLhs` (lengths 5, 2; counters of all 7 terms, `decide`), `lists_baGG3`.
- T4: `gg_counters`, `gg_scalingOrderG`, `gg_mono` at baGGLhs and baGG3; `gg_raw` at baGG3, and inside `A1_keeps` (baGGLhs, κ = 0) and `A1_gains` (baGG4, three internal vertices, κ = 1, `ord A1 = ord Γ + 2`).
None degenerate: nonempty index sets, nonempty solid lists, t ∈ (0,1), both κ cases exhibited. PASS.

## 5. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Graph.BAGGOp 2>&1 | grep -E "error|Build completed"; echo exit $?
Build completed successfully (3785 jobs).
exit 0
$ grep -E "^(warning|error):" build.out | grep -c BAGGOp
0
$ lake env lean ax.lean     # #print axioms, 13 public declarations
RBM.Graph.BAGraph.gg2: [propext, Classical.choice, Quot.sound]
RBM.Graph.BAGraph.gg4: [propext, Classical.choice, Quot.sound]
RBM.Graph.baExpFrame_gg: [propext, Classical.choice, Quot.sound]
RBM.Graph.BAexpFrameE: [propext, Classical.choice, Quot.sound]
RBM.Graph.baExpFrameE_holds: [propext, Classical.choice, Quot.sound]
RBM.Graph.gg_counters: [propext, Classical.choice, Quot.sound]
RBM.Graph.gg_raw: [propext, Classical.choice, Quot.sound]
RBM.Graph.gg_scalingOrderG: [propext, Classical.choice, Quot.sound]
RBM.Graph.gg_mono: [propext, Classical.choice, Quot.sound]
RBM.Graph.BAGGOpInst.lists_baGGLhs: [propext, Classical.choice, Quot.sound]
RBM.Graph.BAGGOpInst.lists_baGG3: [propext, Classical.choice, Quot.sound]
RBM.Graph.BAGGOpInst.A1_keeps: [propext, Classical.choice, Quot.sound]
RBM.Graph.BAGGOpInst.A1_gains: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2410-check.lean; echo $?
0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom " RBM3D/Graph/BAGGOp.lean | wc -l
0
```
Full `lake build` (with `#assert_rbm_axioms`) is left to the hub at merge (CLAUDE.md §3(A)5).

## 6. Paper deltas
```
$ grep -nE "D402|GGraisesord" docs/paper-deltas.md | cut -c1-60
122:`eq:GGraisesord` 将来同样处理。
1361:- **D402（T2161a）**：`GGGamma`（`B:393-405`）前两个和里的系数 `S^+_
1571:- **D612（T2288a–e）**：见 §107 (3)：`(eq:GGraisesord)`（`B:98-100`）
```
- Non-strict order (`ord Γ ≤ ordG T`; A1 keeps the order iff κ = 0) vs `(eq:GGraisesord)` "strictly increases": proposed as **T2410a** (prove report (d)); related D612 and pending T2398b.
- Coefficient `W − 1 = M⁺S⁺` in the first two sums: D402 (existing). Third-sum split `δ + M⁺S⁺` into gg2/gg4: proposed as **T2410b** (bookkeeping).
Coverage complete. PASS.

## 7. Observations (no verdict effect)
- The instances use W = 1 and g0 = 0 (M scalar), as the merged `BAGGExpInst`; the theorems themselves carry no restriction on W or g0 (preflight checked BASelf numerically at g0 = 1/64, 1).
- `gg_scalingOrderG` gives only the lower bound `ord Γ ≤ ordG T`; per-partition-member orders (T2395 design §3 (b) table) are not a target and are listed as not covered in the prove report (d).

## Verdict
T1 PASS · T2 PASS · T3 PASS · T4 PASS · T5 (C1/L5) PASS · T6 instances PASS · T7 registry: none, check file compiles.
**T2410: PASS.**
