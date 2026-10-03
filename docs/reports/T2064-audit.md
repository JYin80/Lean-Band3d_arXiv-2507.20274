Auditor model: claude-opus-5-5

# T2064 audit (round 1) — S1-05 `RBM3D/Gauss/LoopFlowStein.lean`

Written Sat Oct  3 20:07 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2064-audit1`, detached at `t/T2064` = `0285caf`; merge-base with main `a9ad27c`, main = `40f70b9`.
Pin (ticket + ST1-COMMON item 6): each ported public statement equals RBM2D `c9a24cf` after renaming R1-R4 and the `d`-exponents. Targets T1-T4 below.

## 1. Statement vs pin (independent script diff)

Script `scratchpad/T2064/audit_diff.py` (mine, written for this audit): comments stripped; theorem = text up to `:=`, def = full body; RBM2D side renamed `Z2 L→Zd d L`, `LoopIdx→Loop.LoopIdx`, `Coord→CoordF`, `gvar L W→gvarF d L W g`, `P L W→PF d L W g`, `Gsig→Gres`, `gloop→loopL`, `spectralZ→zt`, `spectralM→mE`, `X L W→X d L W`, `spectralWordBound/driftA/driftD W→… d W`, `((W:ℝ)⁻¹ ^ 2)→((W:ℝ)^d)⁻¹`, `(L*W)^2→(L*W)^d`; then token diff.
```
$ python3 audit_diff.py src_{LoopFlowCoordinateChain,LoopFlowSteinExpectation,LoopFlowDerivativeEnvelope,LoopExpectationDerivative}.lean .../LoopFlowStein.lean
DIFF BlockMat
    replace (L => (d L
DIFF Xblock_eq_sum_coordinates
    insert  => blockMat d L W
    replace ω).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm => ω)
DIFF time_direction_eq_coordinate_sum            [same blockMat/submatrix token pair]
DIFF wordDirectionMap_time_eq_coordinate_sum     [same]
DIFF gsigFlowDeriv_split                         [same]
DIFF loopWordDeriv_split                         [same]
DIFF trace_wordDirectionMap_time_eq_coordinate_sum [same]
MISSING spectralWordBound_nonneg (private)
DIFF integrable_coord_smul_of_bounded
    replace (g => (f   ... (local binder names g→f, hgm→hfm, hgb→hfb)
31 SAME, 8 DIFF, 1 MISSING; RBM3D-only: ['loopFlowSteinLoop', 'loopFlowSteinLoop_wf', 'loopFlowSteinCoord']
```
Reading of the residuals:
- `blockMat d L W (Xmat d L W ω)` vs `(Xmat ω).submatrix (splitEquiv).symm (splitEquiv).symm`: definitional; the file carries `example … := rfl` at line 116 and it compiles (build below).
- `BlockMat`: private abbrev, gains `d`. `integrable_coord_smul_of_bounded`: private, bound-variable rename only (`g` is now the model parameter).
- `spectralWordBound_nonneg` (RBM2D private) not ported: `grep -c spectralWordBound_nonneg src_*.lean` gives only its definition, so it has no use there.
- The four targets T1-T4 are all in the 31 SAME. So are the definitions they use: `spectralWordDeriv`, `gsigSpectralFlowDeriv`, `flowWindow`, `flowDerivativeEnvelope`, `spectralWordBound` (`driftA`, `driftD` are SAME too).

RBM2D target headers (`git show c9a24cf:…`, lines 193 / 105 / 295 / 87) next to the RBM3D ones (file lines 240 / 706 / 551 / 875). The hypotheses are `|E|<2`, `0<u`, `u<1`, `I.WF`, plus `v ∈ flowWindow u` for T2, in the same order in both. The quantifier order is the same: `(d L W) [NeZero L] [NeZero W] (g)`, then `{E u}`. The one statement difference is the law `PF d L W g` with a free real `g`; for `g` arbitrary this is a uniform generalisation of RBM2D's fixed `P L W`. It is `PF := Measure.infinitePi (fun c => gaussianReal 0 (gvarF d L W g c))` (`FineModel.lean:97`), the paper's `(bandcw0)` law with profile `S_xy = W^{-d} S^B(g)` (`FineModel.lean:47`).
- d-exponents: the only `d = 2` exponents in the four sources are `(W:ℝ)⁻¹^2` and `(L*W)^2`. They are replaced by `((W:ℝ)^d)⁻¹` (the merged `Eblk` bound) and `(L*W)^d` (= `card (Vtx d L W)`). Their only effect is on the constants of `flowDerivativeEnvelope`/`spectralWordBound` and on proof-internal bounds.

T1 `loop_flow_derivative_actual_coordinate_chain`: statement = pin. PASS on item 1.
T2 `norm_samplewise_loop_flow_derivative_le_envelope`: statement = pin. PASS on item 1.
T3 `expected_samplewise_loop_flow_derivative`: statement = pin + `g` (T2064a). PASS on item 1.
T4 `deriv_integral_gloop_HflowBlock_spectralZ`: statement = pin + `g` (T2064a). PASS on item 1.

## 2. Vacuity, hidden hypotheses, cycles

- No `structure`/`class` is declared in the file. No target takes a `Prop`-valued predicate, a pin, or an external hypothesis. The only hypotheses are deterministic (`|E|<2`, `0<u<1`, `I.WF`, `v∈flowWindow u`), so no limit check is needed (TEAM §8 l.14 n/a).
- Imports: `RBM3D.Gauss.{LoopCoordinate,Stein,SteinMatrix,DominationAt}` and `Mathlib.Analysis.Calculus.ParametricIntegral`. All are merged modules; none is `RBM3D` itself or an ST-2…ST-6 file. The new file is imported by no one, so there is no cycle.
- `grep -nE "set_option|unsafe|opaque|implemented_by|extern|@\[csimp" LoopFlowStein.lean` → no output.
- `RBM3D/Test/Axioms.lean` is unchanged (`git diff main...HEAD -- RBM3D/Test/Axioms.lean | wc -l` → `0`). That is consistent: there is no structural or owed predicate.

## 3. Compiled nonempty instances (file lines 897-1006, inside the module build)

Data: `d=3, L=3, W=2` (N = 216), `g=1`, `E=3/10`, `u=1/2`, loop `⟨[true,false],[![0,0,0],![1,2,0]]⟩` with `WF := rfl` (two charges, two distinct labels). Every hypothesis is discharged by `norm_num`/`rfl`; no pin is left open.
- T1: `example (ω : Ω 3 3 2)` := `loop_flow_derivative_actual_coordinate_chain 3 3 2 ω (E := 3/10) (u := 1/2) (by norm_num [abs_lt]) (by norm_num) (by norm_num) loopFlowSteinLoop loopFlowSteinLoop_wf`.
- T2: the same data at `v = 3/4 = (1+u)/2`, the right end of the window `[1/4,3/4]`; `hv` by `simp only [flowWindow, Set.mem_Icc]; norm_num`.
- T3, T4: `example :` at `PF 3 3 2 1`, `… 3 3 2 1 (E := 3/10) (u := 1/2) …`.
- Extra instances: `integrable_flowDerivativeEnvelope`, `hasDerivAt_integral_…`, and `stein_gloop_first_coordinate_derivative` at the off-diagonal coordinate `(![0,0,0],![1,0,0],true)`.
None is degenerate: N = 216, the window is nondegenerate, the loop has length 2, and `ω` is universally quantified over a nonempty space (no `False` premise). Verdict on item 3: PASS for T1-T4.

## 4. Build and axioms (audit worktree)

```
$ lake build RBM3D.Gauss.LoopFlowStein
Build completed successfully (3303 jobs).
build exit=0
$ lake env lean scratchpad/T2064/ax.lean      (import RBM3D.Gauss.LoopFlowStein; #print axioms …)
'RBM.Gauss.loop_flow_derivative_actual_coordinate_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.norm_samplewise_loop_flow_derivative_le_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.expected_samplewise_loop_flow_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.deriv_integral_gloop_HflowBlock_spectralZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.hasDerivAt_integral_gloop_HflowBlock_spectralZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.integrable_flowDerivativeEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ registry pre-check: scratchpad/T2064/pre.lean = import RBM3D; import RBM3D.Gauss.LoopFlowStein; #assert_rbm_axioms
axiom audit: 2473 theorems, 1052 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
precheck exit=0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " LoopFlowStein.lean | wc -l
       0
$ git diff --name-only main...HEAD
RBM3D/Gauss/LoopFlowStein.lean
$ name-clash: 34 public names, git grep -lw against main 40f70b9 (RBM3D/*.lean, RBM3D.lean)
hits on main 40f70b9: 0
```
- Only the sole writable file is touched, and no frozen signature is modified (no merged file is in the diff).
- The branch base `a9ad27c` is 6 commits behind main. The commits since then add no clashing name (grep above). The hub's full build at merge settles this.

## 5. Paper-delta coverage

- `g`-parametrised law (T3, T4, and 5 non-target lemmas): proposed as **T2064a**. It mirrors signed D68 (= T2037a, `docs/paper-deltas.md:378`). Covered.
- `blockMat` for `submatrix` (rfl), and `d` explicit in `spectralWordBound`/`driftA`/`driftD`: proposed as **T2064b** (notational). Covered.
- Constants `W^{-d}`, `(LW)^d` in `flowDerivativeEnvelope`: these are Lean-internal majorant constants, not paper statements. They are rule R3 replacements, listed in prove report (a) rows 1-2 and in the narrative. No further delta is needed.

## 6. Observations (no statement/instance/build/axiom/delta effect)

- O1. Prove report (a) row 4 correctly notes that the ticket's phrase "variance `W^{-d}`" holds only as `S_ii ≤ W^{-d}` (equality iff `g = 0`). Statements carry `gvarF` abstractly, so nothing changes.
- O2. RBM2D HEAD `9e0f275` deleted T1 and `flowWindow_mem`. The ticket pins `c9a24cf`, so both are correctly kept.
- O3. Prove report §(b) prints `full lake build` before the root import; the new module is covered by the pre-check reproduced above.

## Verdict

| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| T1 `loop_flow_derivative_actual_coordinate_chain` | = pin | none | compiled, nondegenerate | ok | n/a | **PASS** |
| T2 `norm_samplewise_loop_flow_derivative_le_envelope` | = pin | none | compiled, `v=(1+u)/2` | ok | n/a | **PASS** |
| T3 `expected_samplewise_loop_flow_derivative` | = pin + `g` | none | compiled, `PF 3 3 2 1` | ok | T2064a | **PASS** |
| T4 `deriv_integral_gloop_HflowBlock_spectralZ` | = pin + `g` | none | compiled, `PF 3 3 2 1` | ok | T2064a | **PASS** |

Ticket T2064: **PASS**. No dispatcher sign-off needed.
