Auditor model: claude-opus-5-5
# T2472b (BA-L L3d4b, `RBM3D/Graph/BAProvB.lean`): audit round 1, written Tue Oct 13 00:06:19 UTC 2026
Audited: `t/T2472b` at 0c7e272e in the detached worktree `RBM3D-wt/T2472b-audit1`; ticket `docs/tickets/T2472.md` (targets 5 (b), 6, 7, 8 (a)(b), 10; split pre-signed, confirmed at `T2472-1a-audit.md`); statements fixed at the 1a-audit (probe `RBM3D/Probe/T2472Pins.lean`, 1a-audit §3).

## 1. Diff confinement
```
$ git diff --name-only main...t/T2472b          # main 0f3ecb6b
RBM3D.lean
RBM3D/Graph/BAProvB.lean
RBM3D/Probe/T2472Pins.lean        (1a probe, sole writable "1a only, never merged"; unchanged vs t/T2472: `git diff t/T2472 HEAD --stat -- RBM3D/Probe` empty)
$ git diff main...t/T2472b -- RBM3D.lean
@@ -541,6 +541,7 @@ import RBM3D.Graph.BALocReg2
 import RBM3D.Graph.BAProv
+import RBM3D.Graph.BAProvB
 import RBM3D.Chain.StepDecompGen
```
No merged file edited (`BAProv.lean` = L3d4a, untouched); no frozen signature touched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BAProv RBM3D.Graph.BAProvB
✔ [3953/3953] Built RBM3D.Graph.BAProvB (12s)
Build completed successfully (3953 jobs).          exit=0, 0 error lines
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |^inductive|^structure|maxHeartbeats" RBM3D/Graph/BAProvB.lean | wc -l
0
$ lake env lean T2472b/check_on_branch.lean   # check file + `import RBM3D.Graph.BAProvB` + 5 examples + 16 #print axioms
exit=0, error lines 0
$ grep -o "depends on axioms: \[[^]]*\]" check.out | sort | uniq -c
  16 depends on axioms: [propext, Classical.choice, Quot.sound]
```
The 16: `ba_localregularXP baEngineProv_imp_localregularX baProv_stepPos baProv_exists BAProv_exists_ne ba_localregularXP_ne BAWExp.twist BAProv_frameStep_posW BAProv_lw_W BAProv_gg_W BAProv_lanlw_W BAProv_macroA_W BAProv_macroB_W BAProv_twist_EW BAProv_startOuts_good BAProv_start_W`.

## 3. Statements
Script diff (`diff.py`: docstrings/comments stripped, whitespace normalised; theorems cut at `:=`) of the file against the probe texts fixed at the 1a-audit:
```
$ python3 diff.py RBM3D/Probe/T2472Pins.lean RBM3D/Graph/BAProvB.lean
BAProvStepPos SAME
BAEngineProv SAME
baEngineProv_imp_localregularX DIFF
  probe: (h : BAEngineProv) : T2472_LocRegXClosed
  file : (h : BAEngineProv) : BAProv_LocRegXClosed
T2472_LocRegXClosed(probe) vs BAProv_LocRegXClosed(file): SAME
```
The only DIFF is the name of the conclusion def; its body is SAME, and against the binding check pin (target 8 (b)) the check compile on the branch contains (exit 0):
```
example : T2472_LocRegXClosed := baEngineProv_imp_localregularX ba_localregularXP
example : T2472_LocRegXClosed = BAProv_LocRegXClosed := rfl
example : T2472_FxyDUniv := @fxyValD_univ          example : T2472_FxyDUnion := @fxyValD_union          example : T2472_Bridge := @baProv_bridge
```
Fixed texts (file):
```
def BAProvStepPos (d : ℕ) : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))), BALocStep P L → P.g.Normal →
    ∃ ps : List (BAProvOut P), ps.map (·.Q) = L ∧ (∀ o ∈ ps, o.ExtOK ∧ o.Molecular) ∧ BAWExp d P ps
def BAEngineProv : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))),
    (∀ o ∈ outs ++ errs, o.ExtOK ∧ BACoverBy (P := o.Q) fun k : Fin p => o.π (Sum.inr (localReg_fxyBeta k))) ∧
    BALocRegConcl p c K0 d D (outs.map (·.Q)) (errs.map (·.Q)) ∧
    (∀ o ∈ outs ++ errs, p ≤ o.Q.g.waved.countP (fun e => !e.col)) ∧
    BAWExp d (baPG (BAGraph.ofLGraph (fxyPowGraph p))) (outs ++ errs)
theorem baProv_stepPos (d : ℕ) : BAProvStepPos d
theorem ba_localregularXP : BAEngineProv
```
Target 7 (`baProv_exists`, not a G5-b item; 1a-audit §3: band twin of `lwProv_exists` `LWProv:1560` with `BAWExp`/`BAProvOut`, no tags):
```
theorem baProv_exists (d : ℕ) (K : ℤ) (Γ : BAPGraph (Fin 2)) (hN : Γ.g.Normal) :
    ∃ oP eP : List (BAProvOut Γ), (∀ o ∈ oP ++ eP, o.ExtOK ∧ o.Molecular) ∧ BAProv_Lvl1Body d K Γ (oP.map (·.Q)) (eP.map (·.Q)) ∧
      BAWExp d Γ (oP ++ eP)
```
`BAProv_Lvl1Body` (`BAProvB:812-817`) is the body of `BAlvl1Lemma` (`BALvl1C:53-58`) at `E = Fin 2`, text-for-text (read side by side); the file checks it by elaboration: `example (h : BAlvl1Lemma d) … : ∃ outs errs, BAProv_Lvl1Body d K P outs errs := h K P hN` (`:945`), which compiles. The band's `∀ m t0, lwEngine_Exp …` (tag form) is replaced by the `BAlvl1Lemma` conclusion as the ticket's target 7 states ("the conclusion of `BAlvl1Lemma` … for `oP.map (·.Q)`, `eP.map (·.Q)`, and `BAWExp Γ (oP ++ eP)`").
Target 5 (b): `BAProv_lw_W`, `_gg_W`, `_lanlw_W`, `_macroA_W`, `_macroB_W` (the five `BAFrameStep` kinds `weight`, `gg`, `edge`, `within`, `ggSplit`), `BAProv_twist_EW` + `BAWExp.twist` (twist), `BAProv_frameStep_posW` (`BAFrameStep P F → BAProvPosW d P F` under `∀ e ∈ P.g.dotted, e.eq = false`, implied by `Normal`). Premises of each `_W` (read from the signatures): `3 ≤ L`, `BASelf d L g0 Em m`, `0 ≤ t`, `t < 1`, the edge conditions of the matching `BAFrameStep` constructor, an arbitrary real weight `Wt` on all labellings and `ℓe`; conclusion `∫ Γ.valW … Wt ℓe = Σ_T ∫ T.valW … (Wt ∘ (· ∘ owxEmb k)) ℓe`. This is the C1 binder of `BAWExp` (`BAProv:145-149`) and the ticket's (iii) per-labelling form. No `M = mI`, no smallness of `g`.
Quantifier order and parameters: `BAEngineProv` keeps `p c (0<c) K0 d D` outside, the data `L W g0 Em t m` inside `BALocRegConcl`/`BAWExp` exactly as the pin; `d` is the same dimension in `BALocRegConcl` and `BAWExp` (1a-audit §3 row 8 (a)). **Statement: PASS for targets 5 (b), 6, 7, 8 (a), 8 (b).**

## 4. Hidden hypotheses, vacuity, cycles
```
$ grep -cE "^structure|^class|^inductive" RBM3D/Graph/BAProvB.lean        -> 0  (BAProvOut, ExtOK, Molecular, BACoverBy, BAWExp are L3d4a's, merged c4b39007, audited there)
$ grep -nE "BAShapeLL|BAFrameStepTN|T2472_Binder" RBM3D/Graph/BAProvB.lean
1033:  have hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN := by      (inside a proof)
$ python3 (public statements of BAProvB, docstrings stripped, theorems cut at `:=`)
public statements scanned: 72 | Sizes/sz.lam/withLam/gK hits: []
```
- The only Prop-def premises of public results: `BAProv_twist_posW (h : BAProvPosW …)` (concluded by `BAProv_frameStep_posW`) and `baEngineProv_imp_localregularX (h : BAEngineProv)` (concluded by `ba_localregularXP`, compiled at `:1135`). `BAProv_Lvl1Body` occurs only as a conclusion; its consumer helper `BAProv_Lvl1Body_spec` is `private` (`:1016`). No unproved `Prop` premise, binder discharged inside the proof of `ba_localregularXP_ne` from the merged `baShapeLL_*_tn`.
- No cycle: imports are `RBM3D.Graph.BAProv`, `RBM3D.Graph.BAShapeO2B` (both on main); `open private` reads only merged privates (`BAWeightOp_core`, `BAWeightOp_sd`, `BAGGOp_core`, `BAExpandW_integrable_PF`, `BALvl1A_data_zero`, `BALvl1A_lwSplit_last`, `BALvl1A_sum_eraseIdx`, `BAEngine_frame_ne_nil`, `BAEngine_integral_comb`, `BAEngine_partition_ne_nil`, `BAEngine_Spec`; `BAProvB:20-24`). No external hypothesis, so no limit check is owed.
- Non-vacuity of `BAEngineProv`: `ba_localregularXP_ne` additionally proves `outs ++ errs ≠ []` (instance below).

## 5. Compiled nonempty instances (section 8, `BAProvB:1124-1234`; all compile in the build of §2)
Data: `d = 3`, `L = 4`, `W = 2`, flow point `(g0P, EP, t0P, m0P)` with `flowP_data` discharging `BASelf`, `0 ≤ t0P`, `t0P < 1`; `3 ≤ 4` by `norm_num`; labels `ℓ0`; weights non-constant (`1` at `ℓ0 0`, `1/2` elsewhere).
| target | line | instance | deterministic hypotheses |
|---|---|---|---|
| 8 (a) | 1132 | `ba_localregularXP_ne 2 (1/4) _ 2 3 10` (lists non-empty) | `0 < 1/4` by `norm_num` |
| 8 (a) | 1143 | `BAWExp.prod` of the engine's non-empty list at the flow point, `p = 2` | all discharged |
| 8 (b) | 1135, 1138 | `baEngineProv_imp_localregularX ba_localregularXP 2 (1/4) _ 2 3 10`; the pinned text proved | none open |
| 6 | 1182 | `baProv_stepPos 3 _ _ locStepB normalB`: `ps ≠ []`, ExtOK, Molecular, `BAWExp` evaluated at the flow point | `BALocStep`, `Normal` merged instances |
| 7 | 1197, 1199, 1229 | `BAProv_exists_ne 3 10 (baPG baGGLhs)`, `baProv_exists 3 3 (twist of P_B)`, the weighted identity at the flow point with `oP ++ eP ≠ []` | `Normal` by `decide` / `normalB` |
| 5 (b) | 1164-1176 | `BAProv_frameStep_posW` at `gg` (`P_A`, 31 outputs), `within` (`P_B`), `ggSplit` (`P_C`), `edge` (`P_E`), `weight` (first start term), each with a non-empty output list | dotted hypothesis by `decide` |
| 5 (b) | 1207-1226 | `BAProv_lw_W`, `_gg_W`, `_lanlw_W`, `_macroA_W`, `_macroB_W`, `BAProv_twist_EW`, `BAWExp.twist` at the merged R1 data and the flow point | edge hypotheses by `decide`/`rfl` |
| start | 1152, 1156 | `BAProv_startOuts 2`: length 16, ExtOK, Molecular, covered; `BAProv_start_W` weighted at the flow point | all discharged |
No `N = 0`, no empty index, no collapsed window, no `False` premise, no large witness. **Instances: PASS (target 10).**

## 6. Paper deltas
Already in `docs/paper-deltas.md:285-287`: T2472a (weight on the start graph carried along maps), T2472b (shadow molecules), T2472c (`BAWExp` pointwise-labelled at `BAlwData`, every real weight). Proposed in `T2472b-prove.md` (d): T2472d (per-labelling expansion vs. expansion of `|f_xy|^p`), T2472e (position-indexed outputs; `BAWExp` and non-emptiness not in `lem:localregular`). The Lean/paper differences of this file (weighted step identities, positions with maps, `BAEngineProv` conjuncts) are covered by T2472a–e. **PASS.**

## 7. Name clash
```
$ for each of the 72 public names of BAProvB: git grep -lwF <name> main -- 'RBM3D/*.lean' 'RBM3D.lean'
names with hits on main 0f3ecb6b: 0
```

## 8. Observations (no RETURN)
- O1 Rule (E): some unpinned public helpers do not carry the stem `BAProv_` (`BAWExp.twist`, `BAWExp.val_identity`, `BAProvPosW`, `ba_localregularXP_ne`); all have 0 hits on main. No statement effect.
- O2 For the merge: `RBM3D/Probe/T2472Pins.lean` is in `git diff main...t/T2472b` (sole writable for the 1a, never merged); bring in only `BAProvB.lean` and the import line.
- O3 Three defs (`BAProv_ppA`, `BAProv_ppB`, `BAProv_qqB`) print `[propext]` per the prove report; subset of the standard three.
- O4 Unchanged from the 1a-audit: the `x ~ y` outputs stay in the lists (`2p ≤ ord`); their M-chain bound is L3d2b's.

## Verdict
| target | verdict |
|---|---|
| 5 (b) weighted identities of the five frame kinds and the twist | PASS |
| 6 `BAProvStepPos`, `baProv_stepPos` | PASS |
| 7 `baProv_exists` | PASS |
| 8 (a) `BAEngineProv`, `ba_localregularXP` | PASS |
| 8 (b) `baEngineProv_imp_localregularX` (= `T2472_LocRegXClosed`) | PASS |
| 10 instances | PASS |
**T2472b (L3d4b): PASS.** No dispatcher sign-off needed.
