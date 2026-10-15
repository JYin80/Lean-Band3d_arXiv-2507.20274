Auditor model: claude-opus-5-5
# T2517 row b (`t/T2517b` @ 35835a36): audit round 1 (Thu Oct 15 10:47:33 UTC 2026)
Scope: row b only (targets 6, 7, 9; target 8 moved to C5 by Decision (1) = DECISIONS §339 (1)). Row-b diff = `db2015e4...t/T2517b`.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2517b-audit1` (detached at 35835a36); integration worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2517b-audit1-int` (detached at `main` ff7bd277 + the row-b patch; scratch, uncommitted).
`<S>` = scratchpad `T2517b/`. Pins: `docs/tickets/checks/T2517-check.lean:158-204`, signed at the 1a-audit
(`T2517-1a-audit.md:18-21, 62`) with every inline body `((g n : ℝ) : ℂ) • PsiI … + gueH (sz.withLam 0) … X ω` replaced by `gueHBA sz g t1 t0 K n X ω`.

## 1. Diff scope
```
$ git diff --stat db2015e4...t/T2517b
 RBM3D.lean               |    1 +
 RBM3D/BA/GUEEq729BA.lean | 1331 ++++++++++++++++++++++++++++++++++++++++++++++
$ git diff db2015e4 t/T2517b -- RBM3D.lean
@@ -649,6 +649,7 @@ import RBM3D.BA.MATrLocalBA
 import RBM3D.BA.GUEKPrim
 import RBM3D.BA.GUEOneLoop
+import RBM3D.BA.GUEEq729BA
 
 /-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/
$ git diff --stat main...t/T2517b      # also lists row a's first commit (stacked base), all sole writable files of T2517
 RBM3D.lean | 2 +,  RBM3D/BA/GUEEq729BA.lean | 1331 +,  RBM3D/BA/GUEOneLoop.lean | 85 +,  RBM3D/Probe/T2517Pins.lean | 142 +
```
`gueHBA` text at the stacked base equals main's merged text (row a, ff7bd277):
```
$ diff <(git show db2015e4:RBM3D/BA/GUEOneLoop.lean | sed -n '45,77p') <(git show main:RBM3D/BA/GUEOneLoop.lean | sed -n '58,90p')   -> no output, rc=0 (gueHBA, _isHermitian, _succ, ol_gueHBA_eq)
```
No merged file, frozen signature or `RBM3D/Test/Axioms.lean` line is touched. Imports of the new file: `RBM3D.BA.GUEOneLoop`,
`RBM3D.Universality.GUEPhase.Eq729A` (no `BA/GUEKPrim`: consistent with Decision (1)).

## 2. Statements against the signed pins (script diff, `<S>/diff2.py`, token level, comments dropped)
```
$ python3 -I <S>/diff2.py docs/tickets/checks/T2517-check.lean RBM3D/BA/GUEEq729BA.lean
T2517_DriftBA (check :158-174, 3 inline bodies -> gueHBA) vs condExp_loop_drift_gueBA: pin tokens 366, lean tokens 366, differing hunks 0
T2517_OneStepBA (check :177-204, 1 inline bodies -> gueHBA) vs eq729_one_stepBA: pin tokens 840, lean tokens 840, differing hunks 0
```
Auditor scratch file `<S>/signed.lean` (uncommitted): `import RBM3D.BA.GUEEq729BA`, the two signed `def T2517_*` texts, then
```
example : T2517_DriftBA := @condExp_loop_drift_gueBA
example : T2517_OneStepBA := @eq729_one_stepBA
$ lake env lean <S>/signed.lean      (audit worktree)   -> EXIT=0, no error/warning line
```
(The unsubstituted check text does not elaborate: `failed to synthesize HAdd (Matrix (Idx d (sz.L n) …)) (Matrix (Idx d ((sz.withLam 0).L n) …))`;
this is the known mismatch that `gueHBA` resolves, signed at the 1a-audit; not a row-b defect.)

Unpinned public declarations, all named in the ticket's targets 6-7 (read in full signature):
- `oneStepEnvelopeGUEOf` (:171): `∀ d L W [NeZero L] [NeZero W] m E, 0 < m.im → ‖m‖ ≤ 1 → I.WF → 0 ≤ u → 0 ≤ Δ → u + Δ < 1 → M.IsHermitian →`
  the `Δ^{3/2}` envelope with `16 (ℓ+3)^4 ((WL)^d)^4 (1 + η_{u+Δ}^{-1})^{ℓ+4}` (band constant, `ztOf`/`etaOf`/`genMatGUEOf` in place of `zt`/`etaT`).
- `condExp_loop_step_gueBA` (:467): `0 < m.im`, `I.WF`, `gridTime … (k+1) < 1` ⟹ conditional mean on `filt (sz.withLam 0) k` = Gaussian integral at `gueHBA … k ω + √Δ X`.
- `eq729FBA` (:531), `eq729eBA` (:538): the `let` bodies `F`, `e` of `T2517_OneStepBA` (the file's `example` :1321 checks `eq729FBA` = inline body by `rfl`).
- `eq729_eG2BA` (:599): algebraic identity for `egtNGUEOf` on 2-loops at any `m`, `M` (no hypothesis).
- `eq729_duhamelBA` (:642): `0 < Im m`, `‖m‖ ≤ 1`, `0 ≤ t₁ ≤ t₀ < 1`, `k < K n`, `J.WF`, integrability of the drift ⟹ same envelope.
Mathematics vs ticket: D1 (ii) substitution table (`zt E ↦ ztOf m E`, `etaT ↦ etaOf m`, `mSigma ↦ mSigOf m`, `|E| < 2 ↦ 0 < Im m ∧ ‖m‖ ≤ 1`,
`gueH sz ↦ gΨ_I + gueH (sz.withLam 0)`, `Pgue sz ↦ Pgue (sz.withLam 0)`) is exactly what the 0-hunk diffs encode; quantifier order and the
loss `Δ^{3/2}`, the recursion `(1 + Δ·2Nρ Λ) B_k + eq729c(N, ρ, Λ, p, Δ)` are the pinned ones. UBA-C1: flow datum `(g, E, m)`, no `sz.lam` (grep below).

## 3. Hidden hypotheses, vacuity, cycles
- No `structure`/`class`/Prop-valued `def` is introduced (public decl list below); no hypothesis sits in a structure field.
- Inputs of `eq729_one_stepBA`: `hX` (1-loop expectation at step `k`, the conclusion form of row a's `gueGrid_expect_oneLoopBA`), `hB`, `hg1`-`hg3`
  (pathwise bounds; C5's PathBounds/HypA twins), `hBk` — the same explicit-hypothesis interface as the merged band `eq729_one_step` (Eq729A:731).
  None is an external (non-paper) input; producers are named in the ticket (coverage rows 8, 15; C5).
- Dependencies: `GUEOneLoop` (merged ff7bd277), `Eq729A`, `Drift`, `Generator`, `OneStep` (merged; read by name or `open private`). Zero importers besides `RBM3D.lean`; no cycle.
```
$ python3 -I <greps> RBM3D/BA/GUEEq729BA.lean        (comments dropped)
C1 regex hits (whole file, comments dropped): 0          # msc|mE|zt|etaT|gueScale|mSigma|envConst|gapK|Kstab3|kTwoGUE(Loop)|UNModel.band|Theta d|SB d|sz.lam|"|E| < 2"
X1-C4 def hits: 0                                        # (def|abbrev|structure) (ztOf|etaOf|mSigOf|genMatGUEOf|egtNGUEOf|gueH|Pgue|BAStab|kTwoGUEBA)\b
V imports: 0                                             # ^import RBM3D.BA.(MainInd|TwistPins|Step6)
GUEKPrim import / baEq729_Kdisc: False False             # target 8 not written (Decision (1))
public decls: ['oneStepEnvelopeGUEOf', 'condExp_loop_step_gueBA', 'condExp_loop_drift_gueBA', 'eq729FBA', 'eq729eBA', 'eq729_eG2BA',
 'eq729_duhamelBA', 'eq729_one_stepBA', 'oneStepEnvelopeGUEOf_check', 'condExp_loop_step_gueBA_check', 'condExp_loop_drift_gueBA_check',
 'eq729_eG2BA_check', 'eq729_duhamelBA_check', 'eq729_one_stepBA_check']
$ for n in <8 public names> GUEEq729BAInst; do git grep -lw $n main -- RBM3D | wc -l; done      -> 0 for each (no clash on main ff7bd277)
$ grep -nE "\bsorry\b|\badmit\b|\baxiom\b|native_decide" RBM3D/BA/GUEEq729BA.lean                -> (no output, rc=1)
```

## 4. Compiled nonempty instances (target 9; `RBM.BA.GUEEq729BAInst`, file :1107-1329, all compiled in the module build)
Data: `d = 3`, `sz0` (`L₀ = 4`, `W₀ = 32`, `N = (W L)^3 = 2097152`, `size0` :1235), `n = 0`, `k = 0`, flow datum `g₀, E₀, m₀`
(`hr0I`: `BAReal` at `κ = 1/2` ⟹ `1/2 ≤ Im m₀` :1127, `‖m₀‖ ≤ 1` :1131 via `BAm_norm_le_one`), `t₁ = 17/20`, `t₀ = 9/10`, `K = 131072`
(`N Δ = 4/5`), loop `(+,−; 0, 1)` (`loop2_wf` by `rfl`).
| target | instance | deterministic hypotheses | left as hypothesis |
|---|---|---|---|
| T6 `condExp_loop_drift_gueBA` | `_check` :1179 | `0 < Im m₀`, `‖m₀‖ ≤ 1`, WF, `0 ≤ t₁ ≤ t₀`, `K ≠ 0`, `k < K`, `u₁ < 1` (`grid_lt` :1135) | none |
| T6 `condExp_loop_step_gueBA` | `_check` :1167 | same | none |
| T6 `oneStepEnvelopeGUEOf` | `_check` :1146 (`d=3`, `L=W=2`, `m = 1/5 + 9i/10`, `Δ = 1/4`, `M = 1`) | all | none |
| T7 `eq729_eG2BA` | `_check` :1196 (`M = diag 2`, `u = 1/2`) | none needed | none |
| T7 `eq729_duhamelBA` | `_check` :1216 | all, incl. drift integrability (`GUEEq729BA_hdrift_int`) | none |
| T7 `eq729_one_stepBA` | `_check` :1288; `example` :1309 (`B = univ`, `p = 1`) | `0<Im m`, `‖m‖≤1`, `0≤t₁≤t₀<1`, `Λ=(Nη(t₀))⁻¹` (rfl), `Λ≤1`, `0≤ρ=1`, `ρΛ≤1`, `NΔ≤1`, `hK2b` (`Λ ≥ 2·10⁻⁶`), `hK3b`, `hKd` (`Kt = Eq729AInst_Kt`, `c' = N c²`), `k<K`, `hBk` (≤ 200, `hBk_inst` :1256) | `hX` only in the example (`hB`, `hg1`-`hg3` trivial at `B = univ`); `hX` = row a target 4's conclusion form (another gate's pin) |
No `N = 0`, empty index, collapsed window (`t₁ < t₀`, `Δ = 1/(20·131072) > 0`) or `False` premise; the witness is not astronomically large.

## 5. Build and axioms
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2517b-audit1 && lake build RBM3D.BA.GUEEq729BA     -> EXIT=0
✔ [3935/3935] Built RBM3D.BA.GUEEq729BA (17s)
Build completed successfully (3935 jobs).
$ grep -c "warning.*GUEEq729BA\|GUEEq729BA.lean.*warning" <S>/build.log      -> 0
$ lake env lean <S>/signed.lean      (#print axioms part)
'RBM.BA.condExp_loop_drift_gueBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.condExp_loop_step_gueBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.oneStepEnvelopeGUEOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.eq729_eG2BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.eq729_duhamelBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.eq729_one_stepBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.condExp_loop_drift_gueBA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.eq729_one_stepBA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.oneStepEnvelopeGUEOf_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.condExp_loop_step_gueBA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.eq729_eG2BA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.eq729_duhamelBA_check' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Integration (row b applied onto `main` ff7bd277, i.e. against row a's merged 1,395-line `GUEOneLoop`):
```
$ git diff db2015e4 t/T2517b > <S>/rowb.patch; git -C <int> apply --3way <S>/rowb.patch   -> apply=0; status: M RBM3D.lean, A RBM3D/BA/GUEEq729BA.lean
$ grep -n "GUEOneLoop\|GUEEq729BA\|assert_rbm" <int>/RBM3D.lean   -> 652:import RBM3D.BA.GUEOneLoop / 653:import RBM3D.BA.GUEEq729BA / 656:#assert_rbm_axioms
$ cd <int> && lake build RBM3D.BA.GUEEq729BA   -> EXIT=0; ✔ [3935/3935] Built RBM3D.BA.GUEEq729BA (21s)
$ cd <int> && lake build                       -> EXIT=0
info: RBM3D.lean:656:0: axiom audit: 15527 theorems, 4758 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, … Build completed successfully (4426 jobs).
```
File size: 1,331 lines (< 1,400 soft, < 2,000 binding stop line).

## 6. Paper deltas
Lean/paper differences of row b and their coverage (proposals in `T2517b-prove.md` (d) 5; row a's `T2517a`/`T2517b` cover Lemma 5.15 and `hoff`):
- free flow datum `(g, E, m)` with `0 < Im m`, `‖m‖ ≤ 1` in the drift, conditional step and one-step recursion; Lean-side envelope constant → candidate `T2517c`.
- carrier: grid walk of `Pgue (sz.withLam 0)` shifted by `g Ψ_I` instead of the Brownian motion (MBM) → candidate `T2517d`.
- the discretized one-step form of (7.29) with explicit inputs `hX`, `hB`, `hg1`-`hg3` is the band layer's interface (Eq729A:731), re-instantiated
  verbatim; the BA-specific part of the change is `T2517c`/`T2517d`. Coverage complete. (Tags are temporary; the dispatcher renumbers, since row a's
  tags `T2517a`, `T2517b` coincide with this row's ticket id.)

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
1. `hX` in the T7 example is at `ρ = 1`, `n = 0` (`‖E F_0 − m₀‖ ≤ Λ² ≈ 10⁻¹¹`); it is not derivable from row a's asymptotic `∀ᶠ n` conclusion at a
   fixed `n` and is kept as the other gate's pin, exactly as the merged band precedent `eq729_one_step_check` (Eq729A:1283). Allowed by §4 step 2.
2. `GUEEq729BAInst` reads four private band-instance helpers (`Eq729AInst_Kt`, `_Kt_three`, `_hKb`, `_hKd`) by `open private`; renaming them in
   `Eq729A.lean` would break this file (prove report (d) 2).
3. Prove report b5 token counts (373/859) differ from this audit's tokenizer (366/840); both report 0 differing hunks.
4. At merge, `git diff main...t/T2517b` lists row a's `GUEOneLoop.lean` (db2015e4 version) and the probe: the hub must apply only `db2015e4...t/T2517b`
   (CONTROL merge log, T2517 row a `done:` line), as the integration check above does; bringing in `t/T2517b`'s `GUEOneLoop.lean` would revert row a.

## Verdict
Target 6 (`condExp_loop_drift_gueBA` = `T2517_DriftBA`, with `oneStepEnvelopeGUEOf`, `condExp_loop_step_gueBA`): **PASS**.
Target 7 (`eq729_one_stepBA` = `T2517_OneStepBA`, with `eq729FBA`, `eq729eBA`, `eq729_eG2BA`, `eq729_duhamelBA`): **PASS**.
Target 8: not in scope (moved to C5, Decision (1)); correctly absent.
Target 9 (instances): **PASS**.
Overall: **PASS**. No dispatcher sign-off needed.
