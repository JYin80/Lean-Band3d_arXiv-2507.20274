Auditor model: claude-opus-5-5
# T2352 audit (round 2): UN-48 `Universality/GUEPhase/HypA` — Fri Oct  9 00:49:34 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2352-audit2` (detached at `t/T2352` = 336dec3, repair of round-1 RETURN on e7b62ba).
Source: RBM2D `Universality/GUEPhase/HypA.lean` at 9e0f275 (round-1 statement diff, unchanged here, see §3).

## 1. Scope, hygiene
```
$ git log --oneline main..t/T2352
336dec3 T2352: repair round 1 (Hyp_Kt_detDom instance: STKbound by stKbound_holds; Hyp_grid instance fully discharged at a concrete path)
e7b62ba T2352: HypA part 4 (compiled instances HypAInst for every target)
254e794 T2352: HypA part 3 (Hyp_Kt_disc, discrete Duhamel formula Hyp_grid)
dced3b8 T2352: HypA part 2 (deterministic K-tilde: Hyp_Kt_detDom, Hyp_Kt_one, one-step error)
60654ee T2352: HypA part 1 (real-analysis and loop-level helpers)
$ git diff --stat main...t/T2352
 RBM3D/Universality/GUEPhase/HypA.lean | 1499 +++++++++++++++++++++++++++++++++
 1 file changed, 1499 insertions(+)
$ git diff main...t/T2352 | grep -nE '^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom ' ; echo hits=$?
hits=1            (nothing found)
$ grep -n '^import' RBM3D/Universality/GUEPhase/HypA.lean
6:import RBM3D.Universality.GUEPhase.Proc
7:import RBM3D.Universality.GUEPhase.EntryTailMain
8:import RBM3D.Loop.KBound
9:import RBM3D.Loop.KLFinal
$ grep -n '^import' RBM3D/Loop/KLFinal.lean
6:import RBM3D.Loop.KLWardIneq
7:import RBM3D.Loop.KBound
8:import RBM3D.Propagator.Prop6Hold
9:import RBM3D.Induction.Step34Pins
10:import RBM3D.Defs.StochDomAt
$ wc -l RBM3D/Universality/GUEPhase/HypA.lean
    1499
```
Only the sole writable file (new; no frozen signature touched). 1499 lines: within the ticket's stop line (over 1500 → RETURN).
`KLFinal` is a merged module that does not import `Universality/`: no cycle.

## 2. Build and axioms
```
$ lake build RBM3D.Universality.GUEPhase.HypA ; grep -nE 'error|warning' build.log | grep -i hypa   (no hit)
✔ [3779/3779] Built RBM3D.Universality.GUEPhase.HypA (7.6s)
Build completed successfully (3779 jobs).
exit=0
$ lake env lean ax.lean     (#print axioms of the 13 targets)
'RBM.Univ.GUEPhase.Hyp_step_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_time_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_time_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_interp_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_exists_loopOf' depends on axioms: [propext, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_eps_le_dev' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_trace_eq_gloop_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_cutGlue_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_Kt_detDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_Kt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_Kt_disc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.Hyp_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

## 3. Statements
The repair touched only the import block and `HypAInst`:
```
$ git diff e7b62ba 336dec3 -- RBM3D/Universality/GUEPhase/HypA.lean | grep '^@@'
@@ -6,6 +6,7 @@ Authors: Jun Yin
@@ -1122,11 +1123,11 @@ end RBM.Univ.GUEPhase
@@ -1339,11 +1340,19 @@ private theorem exists_Kt :
@@ -1351,7 +1360,7 @@ example (hKb : sz0.STKbound Ei) : ∃ Kt : (n : ℕ) → ℝ → RBM.Loop.LoopId
@@ -1392,27 +1401,98 @@ example := Hyp_Kt_disc sz0 Kt0 (t1 := tw1) (t0 := tw0) (K := K64) (n := 0) (M :=
$ (awk-extract every `theorem Hyp_` block at e7b62ba and at 336dec3); diff stm_e7b62ba.txt stm_336dec3.txt
13 target statements: IDENTICAL e7b62ba vs 336dec3
```
So the round-1 script diff against the RBM2D source (port-map renamings only, plus the `Hyp_Kt_detDom`/`Hyp_Kt_one`
departure `hell : L^d(1-t1) ≤ lam²`, `hKb : sz.STKbound E`, `hKinit` on `loopOf σ a` with `STKloop`, as merged
`gueKproc_detDom` (DECISIONS §141)) still holds. Quantifier order, losses and `N = (WL)^d` are as in the source. Statements: PASS for all 13.

## 4. Hidden hypotheses, vacuity, cycles
No new structure; `Sizes` fields are the merged ones; dependencies are merged modules; no cycle. The external
hypothesis `hKb : STKbound` of `Hyp_Kt_detDom` is a merged result (`Sizes.stKbound_holds`, `Loop/KLFinal.lean:243`),
now discharged at the instance (§5).

## 5. Compiled nonempty instances (`RBM.Univ.GUEPhase.HypAInst`)
Unchanged since round 1 (PASS there): `Hyp_step_nonneg/time_ge/time_le/time_mem/interp_bound`, `Hyp_exists_loopOf`,
`Hyp_trace_eq_gloop_one`, `Hyp_cutGlue_le`, `Hyp_eps_le_dev`, `Hyp_Kt_one`, `Hyp_Kt_disc`.

Round-1 item 1, `Hyp_Kt_detDom` (l.1355): `example : ∃ Kt, ∀ ε > 0, ∀ᶠ n, ...` now has **no binder**; `hKb` is
`private theorem hKb0 : sz0.STKbound Ei := Sizes.stKbound_holds sz0 (le_refl 3) (κ := 1/10) (gmax := 1) ...` (l.1344),
the term checked in round 1. Every hypothesis discharged at `sz0` (`N_n = 2^21 (n+1)^18 → ∞`, `κ = 1/10`, `E = 0`). PASS.

Round-1 item 2, `Hyp_grid` (l.1459): closed term at `ω₀ = fun _ _ => 0`, `δ₀ = 1 + ∑_{k<65} |gueDev_k ω₀|`
(`stop0 : gueStop .. δ₀ 0 ω₀ = 64`, proved through `hittingBtwn`), `m = 2`, `k = 40`, `t = t₀`, `M = 4`, constants
`c₀, C_f, C_e, g₄` finite sums of the left sides, `hdisc` by `Hyp_Kt_disc`. Check that the `example`s are fully applied
(not a partial application with a Pi type): scratch copy of the file with `example :=` → `noncomputable def chk… :=`:
```
$ lake env lean chk.lean   (only linter `defProp` warnings besides)
RBM.Univ.GUEPhase.HypAInst.chkDisc :
  ‖Kt0 0 (gridTime tw1 tw0 K64 0 40) { σ := [true, false], a := [0, 1] } -
          Kt0 0 (gridTime tw1 tw0 K64 0 0) { σ := [true, false], a := [0, 1] } -
        ↑(gridStep tw1 tw0 K64 0) *
          ∑ j ∈ Finset.range 40,
            primRhsGUE 3 (sz0.L 0) (sz0.W 0) (Kt0 0 (gridTime tw1 tw0 K64 0 j)) { σ := [true, false], a := [0, 1] }‖ ≤
    3 * ↑4 ^ 6 * ↑((sz0.W 0 * sz0.L 0) ^ 3) ^ 2 * gridStep tw1 tw0 K64 0 * (tw0 0 - tw1 0)
RBM.Univ.GUEPhase.HypAInst.chkGrid :
  gueDmax sz0 Ei tw1 tw0 K64 Kt0 0 2 40 ω0 ≤
    c0 * 1 + 3 * ↑4 ^ 6 * ↑((sz0.W 0 * sz0.L 0) ^ 3) ^ 2 * gridStep tw1 tw0 K64 0 * (tw0 0 - tw1 0) +
          c0 * (gueScale sz0 Ei 0 (gridTime tw1 tw0 K64 0 40))⁻¹ ^ 2 +
        ((∑ j ∈ Finset.range 65, ∑ x, AFj j x) * supOn (fun x => 1) (tw1 0) (tw0 0) +
            (∑ j ∈ Finset.range 65, ∑ x, AEj j x) * supOn (fun x => 1) (tw1 0) (tw0 0)) *
          (gridTime tw1 tw0 K64 0 40 - tw1 0) +
      c0 * supOn (fun x => ∑ j ∈ Finset.range 65, Qj j) (tw1 0) (tw0 0) * √(gridTime tw1 tw0 K64 0 40 - tw1 0)
'RBM.Univ.GUEPhase.HypAInst.chkGrid' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
The conclusion is the theorem's conclusion: all 23 hypotheses of `Hyp_grid` (`ht10 … hkt`, incl. `h0, hM, hq, hF,
heG, hkσ`) are discharged. Nondegenerate: `k = 40 ≥ 1`, `m = 2`, window `t₀ - t₁ > 0`, `K = 64`, `N = 2^21`. PASS.

## 6. Paper deltas
`grep -c T2352 docs/paper-deltas.md` → `0`. Candidate `T2352a` (prove report l.241) covers the only statement
difference (`hell`, `hKb`, `hKinit`/`STKloop`, `mSigma`); the repair changes no statement. Coverage complete.

## 7. Observations (no RETURN)
- At `ω₀ = 0`, `gueH .. ω₀ = 0` (`Grid.lean:77`: `√t₁ X(ω 0) + √(Δ/N) ∑ X(ω i)`), so the `Hyp_grid` instance is a
  zero-matrix path; it is a legitimate point of `PathΩ sz0` and the theorem is deterministic per `ω`, so this is not a
  degeneracy of the index sets, window or premises. The instance uses `δ₀` instead of `gueDelta` (δ is a parameter).
- `import RBM3D.Loop.KBound` is unused (also imported transitively by `KLFinal`); the ticket lists it.
- File at 1499 lines, one below the stop line; ticket size estimate 1300 exceeded (not a stop condition).

## Verdict per target
| target | verdict |
|---|---|
| `Hyp_step_nonneg`, `Hyp_time_ge`, `Hyp_time_le`, `Hyp_time_mem`, `Hyp_interp_bound` | PASS |
| `Hyp_exists_loopOf`, `Hyp_eps_le_dev`, `Hyp_trace_eq_gloop_one`, `Hyp_cutGlue_le` | PASS |
| `Hyp_Kt_detDom`, `Hyp_Kt_one`, `Hyp_Kt_disc`, `Hyp_grid` | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
