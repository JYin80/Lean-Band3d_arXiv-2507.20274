Auditor model: claude-opus-5-5

# T2037 audit (round 1) — S1-02 `RBM3D/Gauss/LoopCoordinate.lean`
Written Sat Oct  3 15:26:45 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2037-audit1`, detached at `639a4f5` (= `t/T2037`).
Scratch: `<scratchpad>/T2037/{adiff.py,audit_check.lean}`.

## 1. Scope, build, forbidden tokens
```
$ git diff --name-only main...t/T2037
RBM3D/Gauss/LoopCoordinate.lean
$ lake build RBM3D.Gauss.LoopCoordinate 2>&1 | grep -v '^trace' | grep -E "error|warning|Build"
Build completed successfully (3297 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Gauss/LoopCoordinate.lean ; echo rc=$?
rc=1
$ grep -n '^import' RBM3D/Gauss/LoopCoordinate.lean
6:import RBM3D.Gauss.FlowCalculus
```
Only the sole writable file is touched (new file; `RBM3D/Test/Axioms.lean` untouched, no registry line needed: see 4). No frozen signature touched. Imports neither `RBM3D` nor an ST-2…ST-6 file.

## 2. Statements (independent script diff against RBM2D `c9a24cf`)
`adiff.py`: extracts every declaration header (up to `:=` / first match arm) of the five RBM2D files at `c9a24cf` (`git show`), applies R1–R4 and the merged vocabulary (`L W→d L W`, `Coord→CoordF`, `Z2 L→Zd d L`, `BlockIndex→Vtx`, `green H z→Gres H z true`, `Gsig→Gres`, `gloop→loopL`, `LoopIdx→Loop.LoopIdx`, `(W:ℝ)⁻¹^2→((W:ℝ)^d)⁻¹`, `((L*W)^2:ℕ)→((L*W)^d:ℕ)`, `P L W→PF d L W g`, `coordA W→coordA d W`) and compares with the RBM3D headers:
```
$ python3 adiff.py
DIFF integrable_gloop_coordinate_derivatives
  R2': theorem integrable_gloop_coordinate_derivatives (u : ℝ) (c : CoordF d L W) ... (PF d L W g)
  R3 : theorem integrable_gloop_coordinate_derivatives (g u : ℝ) (c : CoordF d L W) ... (PF d L W g)
DIFF measurable_integrable_actual_gloop_coordinate_derivatives
  R2': theorem measurable_integrable_actual_gloop_coordinate_derivatives (u : ℝ) (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) : let D₁ : Ω d L W → ℂ
  R3 : theorem measurable_integrable_actual_gloop_coordinate_derivatives (g u : ℝ) (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) : let D₁ : Ω d L W → ℂ
identical 39 different 2 RBM2D 41 RBM3D 45
only RBM3D: ['loopCoordinateLoop', 'loopCoordinateLoop_wf', 'loopCoordinateOff', 'loopCoordinateDiag']
```
(The two residual diffs are exactly the explicit binder `(g : ℝ)` of the law `PF d L W g`; RBM2D's `P L W` has no parameter.) The `let D₁ … D₂ …` body of `measurable_integrable_actual_…` was compared by hand: RBM2D `LoopCoordinateIntegrability.lean:131-139` vs RBM3D `LoopCoordinate.lean:790-799` — identical after renaming (`gloop L W→loopL d L W`, `P L W→PF d L W g`).
Definition bodies compared by hand (RBM2D vs RBM3D): `gsigCoordinateDeriv` (Deriv:71 / :84), `coordinateWordDeriv` (Deriv:91 / :108), `gsigCoordinateSecondDeriv` (Second:23 / :259), `coordinateSecondWordDeriv` (Second:45 / :286), `coordA/coordD/coordS` (Bounds:23-33 / :425-437), `coordinateFirstWordBound`/`coordinateSecondWordBound` (Bounds:36-46 / :441-452): identical after renaming; `(W:ℝ)⁻¹^2 → ((W:ℝ)^d)⁻¹` (volume factor per `G·E` block, R3). `coordinateBlock`: RBM2D `(coordinateMatrix c).submatrix (splitEquiv).symm (splitEquiv).symm` → merged `blockMat d L W (coordinateMatrix d L W c)` (the merged block reindexing).
All 32 public RBM2D declarations of the five files are present (counted: Deriv 10, Second 7, Green 2, Bounds 4, Integrability 9 = 32; `grep -cE '^(noncomputable )?(theorem|def) '` on the RBM3D file: 32). None dropped; RBM2D privates stay private.

Per target, against the ticket's mathematics (ticket "Key statements"):
| target | hypotheses | exponents / dimension | verdict |
|---|---|---|---|
| `hasDerivAt_gloop_update` | `z.im ≠ 0`, `I.WF` | none | PASS |
| `hasDerivAt_deriv_gloop_update` | `z.im ≠ 0`, `I.WF` | none | PASS |
| `hasDerivAt_deriv_green_HflowBlock_update` | `z.im ≠ 0`; value `2•(G B G B G)`, `G = Gres … true` | none | PASS |
| `norm_gloop_coordinate_derivatives_le` | `0 < η`, `η ≤ |z.im|`, `I.WF`, ∀ω | trace factor `(L W)^d`, `W^{-d}` per edge in `coordA/D/S` | PASS |
| `measurable_integrable_actual_…` | `z.im ≠ 0`, `I.WF`, ∀ `g` | law `PF d L W g` | PASS (generalises RBM2D over `g`; no hypothesis on `g`) |
`d` is a free `ℕ` with no `3 ≤ d` hypothesis; the statements are dimension-generic, so no special case of the general target.

## 3. Hidden hypotheses, vacuity, cycles
No structure-valued hypothesis; every hypothesis is in the signature (table above). The file depends only on merged modules (`RBM3D.Gauss.FlowCalculus` and its imports); no cycle. No external input and no pin hypothesis, so TEAM §8 lesson 14 does not apply.

## 4. Axioms and registry pre-check (auditor scratch file `audit_check.lean`: `import RBM3D`, `import RBM3D.Gauss.LoopCoordinate`, `#print axioms` ×5, one auditor example, `#assert_rbm_axioms`)
```
$ lake env lean <scratch>/T2037/audit_check.lean   (lines starting with RBM names elided)
'RBM.Gauss.hasDerivAt_gloop_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.hasDerivAt_deriv_gloop_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.hasDerivAt_deriv_green_HflowBlock_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.norm_gloop_coordinate_derivatives_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.measurable_integrable_actual_gloop_coordinate_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
axiom audit: 1949 theorems, 835 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
premises found by scanning: 47 (borrowed 2, owed 32, structural 13).
exit=0
```
The targets take no `Prop`-valued premise on sample/matrix/parameters, so no registry line is owed.

## 5. Compiled nonempty instances (file section 5, `LoopCoordinate.lean:821-934`; compiled by the build in 1)
Data: `d = 3, L = 3, W = 2` (`N = 216`), 2-loop `([true,false], [(0,0,0),(1,2,0)])` with `WF` by `rfl`, `u = 1/2`, `z = Complex.I`, `η = 1 = |Im z|`, every sample `ω`, law `PF 3 3 2 1`; coordinates `loopCoordinateOff = ((0,0,0),(1,0,0),true)` and `loopCoordinateDiag = ((0,0,0),(0,0,0),true)`; an `example` proves `coordinateBlock 3 3 2 loopCoordinateDiag v v = 1` (diagonal direction nonzero).
| target | instance | hypotheses discharged |
|---|---|---|
| `hasDerivAt_gloop_update`, `hasDerivAt_deriv_gloop_update` | Off and Diag | `by norm_num` (`Im i ≠ 0`), `loopCoordinateLoop_wf` |
| `hasDerivAt_deriv_green_HflowBlock_update` (with `hasDerivAt_green_HflowBlock_update`) | Off | `by norm_num` |
| `norm_gloop_coordinate_derivatives_le` | Off, `η = 1` | `one_pos`, `by simp` (`1 ≤ |Im i|`), wf |
| `measurable_integrable_actual_…` | Off and Diag, `g = 1` | `by norm_num`, wf |
No `N = 0`, empty index, collapsed window, `False` premise or large witness. Every target has an instance: PASS.
Auditor's extra instance (same scratch file, compiled, exit 0 above): the bound at the provably used coordinate `Diag`, a 3-loop `([+,-,+], [(0,0,0),(1,2,0),(2,1,1)])` (`WF` by `rfl`), `z = 2i`, `η = 1 < 2`:
```lean
example (ω : Ω 3 3 2) :
    ‖Matrix.trace (coordinateWordDeriv 3 3 2 (1 / 2) ω auC (2 * Complex.I) (auI.σ.zip auI.a))‖ ≤
      (((3 * 2) ^ 3 : ℕ) : ℝ) * coordinateFirstWordBound 3 3 2 (1 / 2) 1 auC auI.a.length :=
  (norm_gloop_coordinate_derivatives_le 3 3 2 one_pos auC (by norm_num) auI auI_wf ω).1
```

## 6. Name clashes
```
$ for n in <32 public names of the file>; do git grep -wn -E "(theorem|def|lemma|abbrev) $n" main -- RBM3D; done | wc -l
0
```

## 7. Paper deltas
The only Lean/source statement difference is the explicit `(g : ℝ)` of `PF d L W g` in `integrable_gloop_coordinate_derivatives` and `measurable_integrable_actual_gloop_coordinate_derivatives`; proposed as `T2037a` in prove report (d). The `W^{-d}`/`(LW)^d` exponents are the R3 renaming (volume factors) and are listed in prove report (a)(i)/(b). Coverage complete.

## 8. Observations (no verdict effect)
- O1. `loopCoordinateOff` is used by the Green-function and bound instances. Whether `(i,j,true)` with `i ≠ j` is a live coordinate depends on `idxKey` (`Fintype.equivFin`, not computable), so `B` may be `0` there. Every hypothesis is still discharged at nondegenerate data, and the targets have no hypothesis that depends on `c`. The derivative and integrability instances also use `Diag`, which is provably nonzero, and the auditor's extra instance (5) uses the bound at `Diag`. The prove report's "(a)(ii)" instance (`z = 0.3+0.5i`) differs from the Lean instance (`z = i`); the Lean instance is the one that counts.
- O2. The prove report says the ticket's line counts (163/134/58/252/113) refer to the portmap's `0c1330a`. The target line numbers the ticket cites at `c9a24cf` (150, 138, 59, 218, 131) match the `git show c9a24cf` listing.

## Verdict
All five targets: **PASS**. Ticket T2037: **PASS**. No dispatcher sign-off needed.
