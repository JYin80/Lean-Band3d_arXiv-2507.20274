Auditor model: claude-opus-5-5

# T2077 audit, round 1 (S1-06 `Gauss/LoopGenerator`), Sat Oct  3 22:30:27 UTC 2026

Branch `t/T2077` at 586e57c; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2077-audit1` (detached at 586e57c).
Targets: the ticket's key statements minus the two dead-code ones removed by Amend 1 (DECISIONS §31). Seven remain:
`trace_spectralWordDeriv_eq_sum_original_cuts`, `samplewise_loop_generator_eq_cuts`,
`deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts`, `integral_gloop_HflowBlock_zero`,
`initialLoopValue_all_same`, `initialLoopValue_two_edges`, `adjacentBlockWeight_three`. The other ported public declarations are checked too.

## 1. Statement: script diff against RBM2D `c9a24cf` after the ST1-COMMON item 2 renaming
Script `sd.py` (scratchpad `T2077a/`): it extracts every declaration header up to `:=` from the nine RBM2D files
(`git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/<f>`) and from `LoopGenerator.lean`. It applies
`Z2 L→Zd d L`, `X L W→X d L W`, `P→PF d L W g`, `(W:ℂ)^2→^d`, `(W:ℂ)⁻¹^2→^d`, `2*as.length→d*as.length`, `Gsig→Gres`,
`spectralZ E→zt E`, and `BlockIndex→Vtx d L W`. It then prints the remaining character edits (`*` marks a key target).
```
$ python3 sd.py
RBM2D public/private decls not in RBM3D: ['sum_norm_SB_row', 'sum_norm_integral_sameEdgeCutIntegrand_le', 'sum_norm_integral_pairCutIntegrand_le', 'continuousOn_integral_sameEdgeCutIntegrand', 'continuousOn_integral_pairCutIntegrand', 'continuousOn_list_map_sum', 'continuousOn_expectedSameEdgeCuts', 'continuousOn_expectedPairCuts', 'continuousOn_expectedSpectralCuts', 'continuousOn_expectedLoopCutRHS', 'expected_gloop_hierarchy_integral_unconditional', 'pairedWord', 'green_zero_eq_scalar', 'Gsig_zero_eq_scalar', 'initial_spectral_ne_zero_here']
RBM3D decls not in RBM2D: ['Gres_zero_eq_scalar', 'Eblk_mul_Eblk', 'genLoop', 'genLoop_wf', 'genLoop3', 'genLoop3_wf', 'gen_hE', 'gen_hzim']
IDENT  adjacentBlockWeight_three
DIFF   *deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts ''->'.Loop' | 'g'->'' | ''->'L' | ''->'F' | ''->' g' | ''->'g ' | ''->'F' | ''->' g'
DIFF   *initialLoopValue_all_same ''->'Loop.'
IDENT  initialLoopValue_two_edges
DIFF   *integral_gloop_HflowBlock_zero ''->'.Loop' | 'g'->'' | ''->'L' | ''->'F' | ''->' g'
DIFF   *samplewise_loop_generator_eq_cuts ''->'.Loop' | ''->'F' | ''->'F' | ''->' g' | ''->'g '
DIFF   *trace_spectralWordDeriv_eq_sum_original_cuts ''->'Loop.' | ''->'d ' | 'g'->'' | ''->'L'
DIFF    norm_gloop_any_window_le ''->'.Loop' | 'g'->'' | ''->'L' | ''->'(' | '⁻¹'->'' | '2'->'d)⁻¹'
DIFF    initialLoopValue_eq_trace_product ''->'Loop.' | ''->'(' | ''->' : ℂ)' | 'spectralM'->'mE'
DIFF    continuousOn_integral_gloop_{window,spectralZ,product_*}, integrable_samplewiseLoopGeneratorCuts: same residual classes
IDENT  adjacentBlockWeight_all_same, blockProjectorWord, cutResolventEnvelope, initialGreenScalar, initialLoopValue_one_edge,
       trace_Eblk_eq_one, trace_Eblk_mul_Eblk, trace_blockProjectorWord_cons, map_zip_fst_snd
```
(The output is condensed to one line per residual class; the omitted rows have only the residuals listed above.)
The residuals are only these vocabulary renames: `gloop L W → loopL d L W`, `LoopIdx → Loop.LoopIdx`, `P L W → PF d L W g`
(the law carries `g`), `spectralM → mE`, `spectralEdgeSplits (L := L) → spectralEdgeSplits d L`, `pairedWord` unfolded
to its `foldr` (private), and the envelope factor `W⁻¹^2 → ((W:ℝ)^d)⁻¹`. No hypothesis was added or removed, the
quantifier order is unchanged, and no index range changed.
Dropped declarations: the dead-code chain (Amend 1 / DECISIONS §31). `sum_norm_SB_row` is not aliased (§31). `green_zero_eq_scalar`
and `Gsig_zero_eq_scalar` are replaced by `Gres_zero_eq_scalar`. The only RBM2D consumer is inside the ported files:
```
$ git -C ../RBM2D --no-optional-locks grep -n "green_zero_eq_scalar\|Gsig_zero_eq_scalar" c9a24cf -- RBM2D | grep -v LoopInitialValueScalar
c9a24cf:RBM2D/Gauss/LoopInitialValueProjectionWords.lean:78:      rw [Gsig_zero_eq_scalar L W _ (initial_spectral_ne_zero_here hE) p.1, ih]
```

**d-dimensional exponents against the paper.** Paper `1_2_Intro_model_result.tex:1000-1004` gives (eq:initial_K) and (eq:KMloop):
`M^(k)_{σ,a} = tr ∏ (M(σ_i)E_{a_i}) = W^{-(k-1)d} ∏ m(σ_i) 1(a_1=…=a_k)`. The Lean values are:
`initialLoopValue_two_edges`: `s₁ s₂ · (if a=b then W⁻¹^d)` (k=2); `adjacentBlockWeight_three`: `(W⁻¹^d)^2 = W^{-2d}` (k=3);
`initialLoopValue_all_same`: `W⁻¹^(d·len as)` (k = len as + 1). All three equal (eq:KMloop). The generator coefficient
`W^d` in `samplewiseLoopGeneratorCuts` (lines 235-247, through `SB d L g`) matches (pro_dyncalK) (`W^d Σ_{a,b} … S^{(B)}_{ab} …`).
Independent numeric check (matrix traces, d=3, L=3, W=2):
```
$ python3 -c "...E(a)=diag(W^-d on block a)..."
|Vtx| 216 tr(EaEa) 0.125 W^-d 0.125 tr(EaEb) 0.0
tr(EaEaEa) 0.015625 W^-2d 0.015625 d=2 value W^-4 0.0625
```
The ticket's parenthetical wording does not match the paper in two places:
- It says "`2d` adjacent blocks" for `adjacentBlockWeight_three`. In fact the exponent is `2d`, from two adjacent equal pairs.
- It says "the variance profile `svarF`" for `initialLoopValue_two_edges`. At `u = 0`, `HflowBlock 0 = 0`, so
  (eq:KMloop) contains no variance profile; `svarF`/`SB d L g` enter only through the cut values of the generator.

The Lean follows the paper (CLAUDE.md §5.1, sole source). This is an observation (O1) for the dispatcher to fix in the ticket text. It is not a statement defect.

## 2. Vacuity, hidden hypotheses, cycles
- Structures: `SpectralEdgeSplit` has data fields only (`pre`, `edge`, `post` : lists/pairs; lines 40-43). No `Prop` field.
- New `Prop`: `AdjacentMismatch` (line 601) is a data condition on a label list. It is registered as structural in
  `RBM3D/Test/Axioms.lean`, and it is a hypothesis only of `initialLoopValue_zero_of_adjacentMismatch` (not a key target).
- No external hypothesis and no propagator pin as hypothesis; Amend 1's "PT pins hyp." has nothing to discharge (none of the
  nine RBM2D files takes one). Imports: only the merged `RBM3D.Gauss.LoopFlowStein` and `RBM3D.Hierarchy.ContractionSecondLoop`
  (lines 6-7); there is no cycle.

## 3. Compiled nonempty instances (`LoopGenerator.lean:870-1015`, compiled in §4)
Data: `d=3, L=3, W=2` (216 vertices), `g=1`, `E=3/10` (`|E|<2` by `norm_num`), `u=1/2`, window `[1/4,3/4]`,
`genLoop = ⟨[+,-],[(0,0,0),(1,2,0)]⟩` (WF by `rfl`), and `genLoop3 = ⟨[+,-,+],[(0,0,0)×3]⟩`.

| target | instance | hypotheses discharged |
|---|---|---|
| trace_spectralWordDeriv_eq_sum_original_cuts | l.900, every ω | `hI` = `genLoop_wf` |
| samplewise_loop_generator_eq_cuts | l.911, every ω | `0<1/2`, `1/2<1`, WF by `norm_num`/`rfl` |
| deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts | l.930 | `gen_hE`, `0<u<1`, WF |
| integral_gloop_HflowBlock_zero | l.939 | none needed |
| initialLoopValue_two_edges | l.946 (a=b, value `s₊s₋·2⁻³`), l.954 (a≠b, value 0) | `gen_hE`; `![0,0,0] ≠ ![1,2,0]` proved |
| adjacentBlockWeight_three | l.964, value `(2⁻¹^3)^2` | none needed |
| initialLoopValue_all_same | l.971, 3 equal labels, `2⁻¹^(3·2)` | `gen_hE`, WF, `ha` by `rfl`, `hsame` by `simp` |

Also present: `integrable_…` l.923, `continuousOn_gloop_any_window` l.980, `norm_gloop_any_window_le` l.988 with
`η=(1-3/4)·Im m(3/10)>0` from `spectralM_im_pos`, and `continuousOn_integral_gloop_{product_spectralZ,spectralZ}` l.1000/1009.
The instances are nondegenerate: `N=216`, nonempty block set `Zd 3 3`, window of positive length, and no `False` premise.

## 4. Build, axioms, hygiene, scope (audit worktree)
```
$ lake build RBM3D.Gauss.LoopGenerator
Build completed successfully (3306 jobs).
exit 0          (grep -c warning on the log: 0)
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Gauss/LoopGenerator.lean ; echo $?
1
$ lake env lean ax.lean     (#print axioms of 16 public theorems, condensed)
'RBM.Gauss.trace_spectralWordDeriv_eq_sum_original_cuts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.samplewise_loop_generator_eq_cuts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.integral_gloop_HflowBlock_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.initialLoopValue_all_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.initialLoopValue_two_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.adjacentBlockWeight_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.integrable_samplewiseLoopGeneratorCuts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.initialLoopValue_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.initialLoopValue_zero_of_adjacentMismatch' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.continuousOn_gloop_any_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.norm_gloop_any_window_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.continuousOn_integral_gloop_product_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.continuousOn_integral_gloop_product_spectralZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.continuousOn_integral_gloop_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.continuousOn_integral_gloop_spectralZ' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ lake build            (needed so the root olean sees the branch's registry line; see O2)
Build completed successfully (3819 jobs).
$ lake env lean pre.lean   (import RBM3D; import RBM3D.Gauss.LoopGenerator; #assert_rbm_axioms)
axiom audit: 2584 theorems, 1089 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
exit 0
$ git diff main...HEAD --name-only
RBM3D/Gauss/LoopGenerator.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep "^[+-]"   (one appended registry line, 0 removed lines)
+   `RBM.Gauss.AdjacentMismatch, -- two consecutive block labels of a finite label word differ: a data condition ... (T2077, S1-06; DECISIONS §20)
```
Only the two sole writable files are touched. The registry change appends one line, so no frozen signature changes.

## 5. Paper deltas
- `T2077a` (prove report d.2): the extra explicit `g` of every statement about `PF d L W g` / `SB d L g`. Covered.
- `T2077b` (d.3): exponents `W^{-d}`, `W^{-2d}`, `W^{-d(n-1)}`. These agree with (eq:KMloop); the entry is a record of the RBM2D→d change, not a
  paper difference. Covered.
- No other Lean/paper statement difference was found (§1).

## Observations (not RETURN)
- O1. Ticket wording (§1): "`2d` adjacent blocks" and "`svarF` profile" for the two initial-value statements contradict
  (eq:KMloop). The Lean follows the paper. The dispatcher may correct the ticket text; no statement changes.
- O2. Pre-check run order: in a fresh worktree with the copied main cache, the first `lake env lean pre.lean` (before `lake build`) gave
  `error: axiom aud… [RBM.Gauss.AdjacentMismatch] Classify each of them…` exit 1. The cause was a stale `RBM3D.Test.Axioms`
  olean. After the full `lake build` it gives exit 0, as above and as in the prove report (b.1). This is not a defect.
- O3. The prove report's b.5 statement-diff script crashed (traceback pasted). The diff in §1 above replaces it.
- O4. `initialLoopValue_zero_of_adjacentMismatch` has no instance of its own (not a key target). Its content is shown at
  a≠b by the l.954 instance of `initialLoopValue_two_edges`.

## Verdict
All seven amended targets: **PASS**. The statements equal RBM2D `c9a24cf` after renaming, and the d-exponents match the paper.
There are no hidden hypotheses. Every target has a nondegenerate compiled instance. The build and axioms are clean, and only the sole writable files are touched.
Ticket verdict: **PASS**. No dispatcher sign-off is needed (O1 is a wording fix only).
