Auditor model: claude-opus-5-5

# T2330 audit (UN-33 `Universality/GUEPhase/BoundsA`), round 1 — Thu Oct  8 11:57:22 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2330-audit1` (detached at `t/T2330` = c7bc524; merge-base = main = 7b9fefe).
Scratch files: scratchpad `T2330/eq.lean` (check file + `import …BoundsA` + equality examples + `#print axioms`), `T2330/pre.lean`.

## 1. Diff scope and hygiene
```
$ git diff --stat main...t/T2330
 RBM3D/Test/Axioms.lean                   |   2 +-
 RBM3D/Universality/GUEPhase/BoundsA.lean | 920 +++++++++++++++++++++++++++++++
 2 files changed, 921 insertions(+), 1 deletion(-)
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean   (one line changed; the GUEPathBounds line kept, comment extended)
-   `RBM.Univ.GUEPhase.GUEPathBounds, -- … owner UN-33 `BoundsA` `pathBounds_of_forall_highProbAt`; hypothesis of UN-44/47/50/51)
+   `RBM.Univ.GUEPhase.GUEPathBounds, -- … owner UN-33 `BoundsA` `pathBounds_of_forall_highProbAt`; hypothesis of UN-44/47/50/51; conditional producer `BoundsACheck.pathBounds_of_forall_highProbAt` (T2330))
$ grep -nE "sorry|admit|native_decide|^\s*axiom|set_option|implemented_by|extern" RBM3D/Universality/GUEPhase/BoundsA.lean
54:set_option linter.style.longLine false
55:set_option linter.unusedSectionVars false
$ sed -n 6,8p RBM3D/Universality/GUEPhase/BoundsA.lean   (imports, exactly the ticket's three)
import RBM3D.Universality.GUEPhase.Proc
import RBM3D.Universality.GUEPhase.BootstrapAt
import RBM3D.Universality.GUEPhase.Markov
```
Only the two sole writable files; no merged file touched; no frozen signature changed. Declarations (grep): helpers
`Bounds_*` and `Inst_*` all `private`; public: `BoundsACheck.HC` (l.451), `BoundsACheck.Concl` (l.466),
`Bounds_path` (l.503, namespace `RBM.Univ.GUEPhase`), `BoundsACheck.highProbAt_HC/hA/hB/hD/hF` (l.678-740),
`BoundsACheck.pathBounds_of_forall_highProbAt` (l.751), `BoundsAInst.highProbAt_hF_sz0` (l.875).

## 2. Build and axioms
```
$ lake build RBM3D.Universality.GUEPhase.BoundsA 2>&1 | grep -c error; … | grep BoundsA; … | tail -1
0
(no line mentions BoundsA)
Build completed successfully (3763 jobs).
$ lake build RBM3D 2>&1 | grep -E "error|^Build" | tail -3
Build completed successfully (4138 jobs).
$ lake env lean T2330/eq.lean   (#print axioms part)
'RBM.Univ.GUEPhase.Bounds_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.BoundsACheck.highProbAt_HC' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.BoundsACheck.highProbAt_hA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.BoundsACheck.highProbAt_hB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.BoundsACheck.highProbAt_hD' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.BoundsACheck.highProbAt_hF' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.BoundsACheck.pathBounds_of_forall_highProbAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.BoundsAInst.highProbAt_hF_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
$ printf 'import RBM3D\nimport RBM3D.Universality.GUEPhase.BoundsA\n#assert_rbm_axioms\n' > T2330/pre.lean; lake env lean T2330/pre.lean; echo exit=$?
exit=0
axiom audit: 9921 theorems, 2978 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 143 (borrowed 1, owed 83, structural 41, refuted 6, superseded 12).
```

## 3. Statements against the pins (check file `docs/tickets/checks/T2330-check.lean`)
```
$ python3 -I <docstring-stripped, whitespace-normalized text of `def HC` / `abbrev Concl`: check vs BoundsA.lean>
HC equal: True 716 716
Concl equal: True 912 912
$ grep -n "^example" T2330/eq.lean | cut -c1-150   (appended after `end RBM.Univ.GUEPhase.T2330Check`)
199:example {d : ℕ} (sz : Sizes d) : RBM.Univ.GUEPhase.T2330Check.T2330_Bounds_path sz := @fun τU n0 hn0 E t1 t0 Kt n => @RBM.Univ.GUEPhase.Bounds_path d sz τU n0 hn0 E t1 t0 Kt n
200:example {d : ℕ} (sz : Sizes d) : …T2330_highProbAt_HC sz := by intros; apply RBM.Univ.GUEPhase.BoundsACheck.highProbAt_HC sz <;> assumption
201:example … T2330_highProbAt_hA sz := by intros; apply …BoundsACheck.highProbAt_hA sz <;> assumption
202:example … T2330_highProbAt_hB sz := by intros; apply …BoundsACheck.highProbAt_hB sz <;> assumption
203:example … T2330_highProbAt_hD sz := by intros; apply …BoundsACheck.highProbAt_hD sz <;> assumption
204:example … T2330_highProbAt_hF sz := by intros; apply …BoundsACheck.highProbAt_hF sz <;> assumption
205:example … T2330_pathBounds_of_forall_highProbAt sz := by intros; apply …BoundsACheck.pathBounds_of_forall_highProbAt sz <;> assumption
208:example {d : ℕ} (sz : Sizes d) : @…T2330Check.HC d sz = @…BoundsACheck.HC d sz := rfl
209:example {d : ℕ} (sz : Sizes d) : @…T2330Check.Concl d sz = @…BoundsACheck.Concl d sz := rfl
$ lake env lean T2330/eq.lean > T2330/eq.out 2>&1; echo exit=$?; grep -cE "error" T2330/eq.out
exit=0
0
```
`Bounds_path` is checked by a direct term `@Bounds_path d sz τU n0 hn0 E t1 t0 Kt n` against the pinned Π-type (same
binder order `{τU} n0 hn0 {E t1 t0} Kt n`, then `hτU … h4N`, `{τ τ₁}` position, `ω`, `hA…hF`); its `hC` is the unfolded
body of `HC` (defeq, accepted by elaboration). The two `d`-dependent lines are as pinned: `hellN : ((sz.L n : ℕ) : ℝ) ^ d
* (1 - t1 n) ≤ 1` and the control `gueLmax … 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹` (in `HC`, `hC`, `highProbAt_HC`). No
weakening, specialisation or reordering relative to the pins; parameter order (fixed parameters, then `n`, then `ω`) kept.

## 4. Hidden hypotheses, vacuity, cycles
- No new structure; the only definitions are `HC` (Prop def) and `Concl` (abbrev), both pinned verbatim. Hypotheses are
  all in the signatures.
- Dependencies are merged on main 7b9fefe (`Proc`, `ProcK`, `Markov`, `BootstrapAt`, `Grid`, `PerTimeCalc`, `Path/Stop`);
  the module builds against them (§2). No cycle: BoundsA imports only the three merged modules.
- `pathBounds_of_forall_highProbAt` is conditional on `hmain : ∀ τ > 0, HighProbAt … {ω | Concl … τ n ω}` (explicit; the
  ticket calls it a conditional producer); the registry keeps `GUEPathBounds` owed (§1). The `StochDomAt` inputs of
  `highProbAt_HC/hA/hB/hD` are bootstrap/entry-bound outputs of other gates, explicit hypotheses.
- External hypothesis `Tendsto sz.size atTop atTop` of `highProbAt_hF`: limit check is the discharge at `sz0` by the merged
  `MarkovInst.sz0_size_tendsto_nat` (compiled, §5), plus prove report (a)(ii) `size n = 2^21 (n+1)^18`.
- Joint satisfiability of the twelve deterministic hypotheses of `Bounds_path`: discharged at concrete data (§5).

## 5. Compiled nonempty instances (BoundsA.lean l.767-916, namespace `RBM.Univ.GUEPhase.BoundsAInst`; compiled in §2)
```
$ sed -n 852,856p RBM3D/Universality/GUEPhase/BoundsA.lean
example (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ) :=
  Bounds_path sz0 (τU := 3 / 5) 2 le_rfl (E := E0) (t1 := t1c) (t0 := t0c) Kt 0
    (by norm_num) (by norm_num [E0]) (by norm_num [t1c]) (by norm_num [t1c, t0c])
    (by norm_num [t0c]) (τ := 1 / 10) (τ₁ := 1 / 50) (by norm_num) (by norm_num)
    Inst_hscN Inst_hellN Inst_hsmallN Inst_h4N
$ sed -n 788,790p …   (E0 = 0, t1c = 99/100, t0c = 199/200); sz0 at n = 0: L = 4, W = 32, N = 2097152 (Inst_size_real, l.772)
$ sed -n 861,883p … | grep -E "BoundsACheck|theorem"
  BoundsACheck.highProbAt_HC sz0 E0 t1c t0c 2 (τ₁ := 1 / 50) (3 / 5) (by norm_num)
  BoundsACheck.highProbAt_hA sz0 E0 t1c t0c 2 (τ₁ := 1 / 50) (3 / 5) (by norm_num)
  BoundsACheck.highProbAt_hB sz0 E0 t1c t0c 2 (τ₁ := 1 / 50) (3 / 5) (by norm_num) Kt
  BoundsACheck.highProbAt_hD sz0 E0 t1c t0c 2 (τ₁ := 1 / 50) (by norm_num)
theorem highProbAt_hF_sz0 :
  BoundsACheck.highProbAt_hF sz0 2 MarkovInst.sz0_size_tendsto_nat
  BoundsACheck.pathBounds_of_forall_highProbAt sz0 E0 t1c t0c 2 Kt
```
Plus `Bounds_jump`, `Bounds_rpow_key`, `Bounds_final`, `Bounds_unfreeze` at the numbers `N = 2097152`, `Δ = (1/200)/(N+1)^128`,
`Sg = N³`, `δ = N^{-3/20}` (l.889-915), as the ticket's "Instances" asks. Data are nondegenerate (`d = 3`, `N = 2^21`,
`n0 = 2`, `t₁ < t₀` in the zero-mode regime `L³(1 - t₁) = 16/25 ≤ 1`, `τ₁ < τU/4`). Every deterministic hypothesis is
discharged; what remains open in the examples is `Kt`, `ω`, the pathwise events `hA…hF` of `Bounds_path` (events of the
w.h.p. sources above), the `StochDomAt` inputs (other gates) and `hmain` (conditional producer). `highProbAt_hF_sz0` is
fully closed. No `N = 0`, empty index, collapsed window or `False` premise.

## 6. Paper deltas
`docs/paper-deltas.md`: 0 hits for T2330 (new). Candidates proposed in the prove report (d): T2330a (registry: conditional
producer of `GUEPathBounds`), T2330b (`L^d`, `(W^d)⁻¹` replace RBM2D `L²`, `(W²)⁻¹`; paper `1_2_Intro_model_result.tex:566-570`
gives no d ≥ 3 statement), T2330c (`Bounds_path` inapplicable at the `GridCheck` times, consumers need zero-mode `t₁`),
T2330d (`hC` unfolded vs `HC`). These cover every Lean/paper and Lean/RBM2D difference found in §3.

## 7. Observations (no RETURN)
- The registry scan moves `GUEPathBounds` to "carries nothing yet" because a conditional theorem concludes it (T2330a);
  dispatcher bookkeeping, not a statement defect.

## Verdict per target
| target | verdict |
|---|---|
| `BoundsACheck.HC`, `BoundsACheck.Concl` | PASS (verbatim; rfl to the check copies) |
| `Bounds_path` | PASS |
| `BoundsACheck.highProbAt_HC`, `_hA`, `_hB`, `_hD` | PASS |
| `BoundsACheck.highProbAt_hF` | PASS |
| `BoundsACheck.pathBounds_of_forall_highProbAt` | PASS (conditional producer, as ticketed) |

Overall: **PASS**. No dispatcher sign-off needed.
