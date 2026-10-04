Auditor model: claude-opus-5-5

# T2108 audit (round 1) — S1-27 `Green/LocalLaw` — Sun Oct  4 04:57:41 UTC 2026

Audit worktree `RBM3D-wt/T2108-audit1`, detached at `t/T2108` = `8f518d4` (one commit on `main` `90a2761`). Scratch: `scratchpad/T2108/` (`sdiff.py`, `ax.lean`, `pre.lean`).

## 1. Build, hygiene, scope
```
$ lake build RBM3D.Green.LocalLaw
Build completed successfully (3337 jobs).            [exit 0; no error lines]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|set_option (maxHeartbeats|debug)" RBM3D/Green/LocalLaw.lean
(no output; grep exit 1)
$ git diff --stat main...HEAD
 RBM3D/Green/LocalLaw.lean | 1255 +++  RBM3D/Test/Axioms.lean | 4 +-   (2 files changed, 1258 insertions(+), 1 deletion(-))
$ grep -n "^import" RBM3D/Green/LocalLaw.lean
6:import RBM3D.Green.Pins   7:import RBM3D.Green.CondDom   8:import RBM3D.Green.EntryDom
9:import RBM3D.Green.FlucVanish   10:import RBM3D.Induction.PerTimeCalc
```
Only the two sole writable files. `Axioms.lean`: the last `owedProps` line gets a comma and two lines are appended (`RBM.Green.FixedTimeFAThm`, `RBM.Green.IBPDetThm`, class owed); no other change. No ST-2 import: `Induction/PerTimeCalc` is re-assigned to ST-1 (portmap P.7 row S1-08) and is already imported by merged `Green/EntryDom` (line 9). No frozen signature touched (new file only).

## 2. Axioms and registry pre-check
```
$ lake env lean scratchpad/T2108/ax.lean     # #print axioms of all 33 public declarations
exit 0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out  ->  33
$ grep -vc "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out  ->  0
$ lake build RBM3D.Test.Axioms   # copied cache had main's registry olean
Build completed successfully (2 jobs).
$ lake env lean scratchpad/T2108/pre.lean    # import RBM3D; import RBM3D.Green.LocalLaw; #assert_rbm_axioms
precheck exit 0
axiom audit: 3304 theorems, 1207 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Green.FixedTimeFAThm: 4 [no certificate]
  RBM.Green.IBPDetThm: 4 [no certificate]
```
(Before rebuilding `Test.Axioms` the same pre-check failed with "2 premise(s) … in none of …: [RBM.Green.IBPDetThm, RBM.Green.FixedTimeFAThm]", which shows that the two registry lines are needed and enough.) Class owed is right: FA (`jasdu`) and IBP are results of the proof of (`GavLGEX`) that later tickets (S1-29, S1-30) prove.

## 3. Statements: script diff against RBM2D `c9a24cf` after renaming (ST1-COMMON items 2, 6)
`sdiff.py` extracts each public statement (comments stripped) from `git show c9a24cf:RBM2D/Green/{AvgPins,LocalLaw}.lean` and from the new file, applies R1 (`d : Sizes`→`sz : Sizes d`, `d.`→`sz.`), `SizeTendsto d → Bandwidth d 𝔠`→`sz.Admissible 𝔠 𝔡` (+`𝔡`, D39) and `(d : ℕ)` on the pins, and prints the token hunks that remain (RBM2D => RBM3D):
```
SAME     AvgBoundDetThm
DIFF     FABlkDet: [PerTimeDomAt (Sizes.seqP d) sz.size] => [sz.PrecPT] | [Z2] => [Zd d] | [] => [d] | [] => [d] | [(Sizes.seqHflow d] => [(sz.seqHflow] | [spectralM] => [mE]
DIFF     FARowDet: [PerTimeDomAt (Sizes.seqP d) sz.size] => [sz.PrecPT] | [(Sblk2] => [(svar d] | [] => [n) (sz.lam] | [] => [d] | [(Sizes.seqHflow d] => [(sz.seqHflow] | [spectralM] => [mE]
DIFF     FixedTimeFASeq: [d] => [sz] | [d] => [sz]
DIFF     FixedTimeFAThm: [(((sz.W] => [((sz.W] | [ℝ))⁻¹] => [ℝ) ^ (-(d : ℝ) / 2)]
DIFF     GavLDetFloorThm: [(((sz.W] => [((sz.W] | [ℝ))⁻¹] => [ℝ) ^ (-(d : ℝ) / 2)]
SAME     GavLDetThm
DIFF     IBPDet: [PerTimeDomAt (Sizes.seqP d) sz.size] => [sz.PrecPT] | [spectralM] => [mE] | [(Sblk2] => [(svar d] | [] => [n) (sz.lam] | [] => [d] | [(Sizes.seqHflow d] => [(sz.seqHflow] | [spectralM] => [mE]
DIFF     IBPDetSeq: [d] => [sz]
DIFF     IBPDetThm: [(((sz.W] => [((sz.W] | [ℝ))⁻¹] => [ℝ) ^ (-(d : ℝ) / 2)]
DIFF     LocalLawDetSeq: [PerTimeDomAt (Sizes.seqP d) sz.size] => [sz.PrecPT] | [] => [d] | [] => [d] | [] => [d] | [(Sizes.seqHflow d] => [(sz.seqHflow]
DIFF     LocalLawDetThm: [(((sz.W] => [((sz.W] | [ℝ))⁻¹] => [ℝ) ^ (-(d : ℝ) / 2)]
NEW-ONLY LocalLaw_gbEXPV3Theorem_of_fa_ibp
DIFF     LocalLaw_gexRHS_le_maxLoopPM: [(hL : 3 ≤ L)] => [] | [] => [d] | [] => [d] | [Z2] => [Zd d] | [] => [d] | [25] => [(9 : ℝ) ^ d] | [] => [d] | [2)⁻¹] => [d)⁻¹]
NEW-ONLY LocalLaw_loopFloor_literal_false
DIFF     LoopFloorThm: [ℝ)⁻¹)] => [ℝ)] | [2] => [d)⁻¹]
SAME     asGMcSeq_iff
DIFF     avgBoundDetThm: [] => [(hd : 3 ≤ d)]
DIFF     condDiagBlk: [d] => [sz] | [] => [d] | [] => [d] | [(Sizes.seqHflow d] => [(sz.seqHflow] | [spectralM] => [mE]
DIFF     condDiagBlk_time_zero: [d] => [sz]
DIFF     eta_lower_of_rangeCond: [SizeTendsto d)] => [sz.SizeTendsto)] | [(spectralZ] => [(zt]
SAME     fixedTimeFASeq_time_zero
SAME     gavLDetFloorThm_of_parts
DIFF     gavLDetThm_of_floor: [] => [(hd : 2 ≤ d)]
DIFF     gbEXPV3Theorem_of_gavLDetThm: [] => [(hd : 3 ≤ d)]
DIFF     gbEXPV3Theorem_of_parts: [] => [(hd : 3 ≤ d)]
DIFF     gbEXPV3Theorem_of_ports: [] => [(hd : 3 ≤ d)]
SAME     ibpDetSeq_time_zero
SAME     localLawDetSeq_time_zero
DIFF     localLawDetThm: [] => [(hd : 3 ≤ d)]
SAME     loopDetSeq_mono
DIFF     loopFloorThm: [] => [(d : ℕ)]
DIFF     not_sizeTendsto_bandwidth_of_W_one: [(SizeTendsto d] => [(sz.SizeTendsto] | [Bandwidth d] => [sz.Bandwidth]
DROPPED  AvgPins_one_le_size
DROPPED  W_inv_eq_psi
DROPPED  eta_lower
DROPPED  fa_ibp_apply
DROPPED  fa_premises
DROPPED  fa_premises_psi2
DROPPED  floor_applies
DROPPED  llErrMat_time_zero
DROPPED  psi2
DROPPED  psi_eq_rpow
```
Reading the residual hunks:
* Vocabulary (merged MD layer, ST1-COMMON item 3): `PerTimeDomAt (seqP) size`→`sz.PrecPT`, `Z2`→`Zd d`, `BlockIndex`→`Vtx d`, `Sblk2`→`svar d L W (sz.lam n)`, `spectralM/Z`→`mE/zt`. Fit with the merged consumers is checked by Lean: `avgBoundDetThm` feeds `IBPDet/FARowDet/FABlkDet` into merged `avg_bound_stochDom`/`norm_avgErr_le`, and `gbEXPV3Theorem_of_gavLDetThm` passes `GavLDetThm d` straight into the (`GavLGEX`) clause of merged `GbEXPHypV3` (`Pins.lean:210-219`), whose binders `GavLDetThm` repeats (SAME above).
* **Floor** `W⁻¹ ≤ Ψ` → `W^{-d/2} ≤ Ψ` in `LocalLawDetThm`, `FixedTimeFAThm`, `IBPDetThm`, `GavLDetFloorThm`; `LoopFloorThm` concludes `(W^d)⁻¹ ≤ 4N^εΨ²` (RBM2D `(W⁻¹)²`). Paper:
```
$ sed -n 27p paper/tex/3_5_Loop_Hierarchy.tex | cut -c1-120
Finally, suppose the following estimates hold for a deterministic control parameter $W^{-d/2}\le \Psi_t \le W^{-\e_0}$:…
```
  RBM2D's `W⁻¹` is `W^{-d/2}` at `d = 2` (its own docstring `AvgPins:141-143`: "RBM1D's floor `W^{-1/2} ≤ Ψ` becomes `W⁻¹ ≤ Ψ`"), and `(W⁻¹)²` is the `W⁻²`-type of R3. So both are exponent recounts in the sense of ST1-COMMON item 6 / R3, and they make the Lean floor the paper's. The literal port is false at `d = 3`: `LocalLaw_loopFloor_literal_false` (file:1207) compiles (sz0, `t ≡ 0`, `Ψ = W^{-3/2}`, `ε = 1/18`: `W ≤ 4N^{1/18}` fails). This is not a change beyond item 6, so it needs no dispatcher sign-off. T2108a records the RBM2D→RBM3D difference.
* `25` → `9^d` in `LocalLaw_gexRHS_le_maxLoopPM`: the merged `gexRHS` (`Pins.lean:101-105`) sums over `zdistInf ≤ 1` (the `L^∞` ball, `{0,±1}^d`, `≤ 3^d` points; `LocalLaw_near_card` file:459), so `3^d·3^d`. This bound is derived, not a paper statement. `hL : 3 ≤ L` was dropped, which weakens the hypotheses.
* `hd : 3 ≤ d` on `localLawDetThm`, `avgBoundDetThm`, `gbEXPV3Theorem_of_{gavLDetThm,parts,ports}`, `LocalLaw_gbEXPV3Theorem_of_fa_ibp` (from `giiSeq_of_asGMc`, `giiOmegaSeq`, `norm_avgErr_le`; D201); `2 ≤ d` on `gavLDetThm_of_floor` (`W^{-d/2} ≤ W⁻¹ ≤ N^{-𝔠}` for `Ψ' = max(Ψ, W^{-d/2})`). The `Prop` pins take `d` with no `hd`, like merged `GbEXPV3Theorem d`.
* Quantifier order and the time domain (`∀ n |E n| < 2-κ`, `0 ≤ t n < 1`, `RangeCond` and `Ψ ≤ N^{-a}` as `∀ᶠ`) are unchanged from RBM2D and from `GbEXPHypV3`.
* Dropped declarations: `AvgPins_one_le_size` (merged `Sizes.one_le_size`, `Defs/StochDomAt.lean:130`), `llErrMat_time_zero` (merged `Green/Pins.lean:1242`), and RBM2D's `AvgPinsCheck` instance namespace (`W_inv_eq_psi`, `psi_eq_rpow`, `fa_premises*`, `psi2`, `eta_lower`, `floor_applies`, `fa_ibp_apply`), which section 9 replaces. New public names: `LocalLaw_gbEXPV3Theorem_of_fa_ibp` and `LocalLaw_loopFloor_literal_false` (file-stem prefixed, §3 (E)).
* Every target the ticket names is present (list in section 2: 33 names).

## 4. Hidden hypotheses, vacuity, cycles
* No structure is introduced. The pins are plain `Prop` `def`s whose hypotheses appear in the statement. `localLawDetThm`, `avgBoundDetThm` and `loopFloorThm` are proved outright (their axioms are in section 2). The open inputs are only `FixedTimeFAThm d` and `IBPDetThm d`, which appear as explicit theorem arguments and are registered as owed.
* No cycle: imports are merged `Green/{Pins,CondDom,EntryDom,FlucVanish}`, `Induction/PerTimeCalc`. Nothing proves a pin from itself: `gbEXPV3Theorem_of_ports` = `_of_parts` with `avgBoundDetThm`, `loopFloorThm`.
* External/random hypotheses of the examples: `AsGMcSeq` (`(def_asGMc)`, `ε₀ = 1/40`) and `LoopDetSeq` (`(initialGT2)`). They are the paper's own premises of `lem_GbEXP`. The prove report's (a)(ii) gives the limit check (`W_n^{-1/40} → 0`; floor ratio `W^{-(d-2)} → 0`). At `t ≡ 0`, both are discharged in Lean (`asGMcSeq_time_zero`, `localLaw_inst_loopDet_zero`), so the premises of `localLawDetThm`, `loopFloorThm`, `avgBoundDetThm` are jointly satisfiable.

## 5. Compiled nonempty instances (section 9, file:1037-1203; they compile with the module build in section 1)
Data: merged `sz0` (`d = 3`, `L_n = 4(n+1)`, `W_n = 32(n+1)^5`, `N_0 = 2097152`), `E_n = lemE z_n`, `κ = δ = 1/20`, `𝔠 = 1/6`, `𝔡 = 1/10`, `t ≡ 1/16` or `t ≡ 0`. The data are nondegenerate: no `N = 0`, no empty index set, no collapsed window, no `False` premise.
```
$ grep -n "^example\|^theorem LocalLaw_loopFloor_literal_false" RBM3D/Green/LocalLaw.lean | cut -c1-90
1037:example (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
1047:example : LocalLawDetSeq sz0 (STflowE z0) (fun _ => 0)
1056:example (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
1065:example (ε : ℝ) (hε : 0 < ε) :
1076:example (hIBP : IBPDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹))
1085:example : GavLDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :
1105:example (hG : GavLDetThm 3) (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
1113:example (hF : GavLDetFloorThm 3) (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
1124:example (hFA : FixedTimeFAThm 3) (hIBP : IBPDetThm 3)
1137:example (hFA : FixedTimeFAThm 3) (hIBP : IBPDetThm 3)
1150:example : LoopDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :
1155:example : LocalLawDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ) 
1161:example : LocalLawDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ)⁻
1172:example : ∀ᶠ n : ℕ in atTop, ((sz0.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤
1179:example :
1190:example (E u : ℝ) (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)) :
1197:example : gexRHS 3 3 1 0 (1 / 2) 0 0 0 ≤
1207:theorem LocalLaw_loopFloor_literal_false :
```
Each endpoint theorem, with its instance:
* `localLawDetThm`: L1037 at `t ≡ 1/16` keeps only `AsGMcSeq` and `LoopDetSeq` as hypotheses; it discharges `Admissible`, bulk, `0 ≤ t < 1`, `RangeCond`, `c > 0` and the floor `W^{-3/2} ≤ W⁻¹`. L1047 at `t ≡ 0` has no hypothesis left (`Ψ = W^{-3/2}`, the floor with equality).
* `loopFloorThm`: L1056 at `1/16`, L1065 at `t ≡ 0` with no hypothesis left. `avgBoundDetThm`: L1076 at `1/16` keeps the FA/IBP outputs; L1085 at `t ≡ 0` has no hypothesis left.
* Wiring theorems `gbEXPV3Theorem_of_gavLDetThm` (L1105), `gavLDetThm_of_floor` (L1113), `gavLDetFloorThm_of_parts` (L1124), and `gbEXPV3Theorem_of_parts`/`_of_ports`/`LocalLaw_gbEXPV3Theorem_of_fa_ibp` (L1137) are applied at `sz0`, `t ≡ 1/16`, `Ψ = W⁻¹`, `a = 1/6`. Every deterministic hypothesis is discharged. The hypotheses left are the pins of other gates (`FixedTimeFAThm 3`, `IBPDetThm 3`, or `GavLDetThm 3`/`GavLDetFloorThm 3` where the target consumes them) and the random premises `AsGMcSeq`, `LoopDetSeq`.
* `LocalLaw_gexRHS_le_maxLoopPM`: L1190 at the `sz0` model matrix (`L = 4`, `W = 32`). The `_time_zero` lemmas, `asGMcSeq_iff`, `loopDetSeq_mono`, `eta_lower_of_rangeCond` and `not_sizeTendsto_bandwidth_of_W_one` are at L1150-1179 with no hypothesis left.
Result: an instance exists for every endpoint, none is degenerate, and all compile.

## 6. Paper deltas
* The new file's statements match the paper: floor `W^{-d/2} ≤ Ψ_t` (`3_5:27`) and `W^{-d}` (`3_5:24`). Two Lean/paper differences remain, both inherited from RBM2D and merged pins: there is no upper window `Ψ ≤ W^{-ε₀}` in `LocalLawDetThm` (Lean is more general), and `Ψ ≤ N^{-a}` comes from merged `GbEXPHypV3`. Candidate **T2108a** in prove report (d.1) records the floor/loop-floor change against RBM2D. `hd` and `Admissible` are covered by signed D201 and D39 (prove report (d.5)). No uncovered difference found.

## 7. Observations (no verdict effect)
1. Ticket text: "near set has `2d + 1` points" is the `zdistD` count. The merged `gexRHS` uses `zdistInf`, which gives `3^d`/`9^d`/`9^d+1`. The prover followed the merged definition (prove report (d.2)), and the Lean bound is checked. The ticket text needs a dispatcher correction only.
2. Prove report (d.1) asks for sign-off on T2108a. The audit finds the change within ST1-COMMON item 6 ("renaming and exponents") and R3, and it matches `3_5:27`. The literal port is compiled false. The audit therefore does not require sign-off, and the dispatcher numbers T2108a as usual.
3. The pre-check in an audit worktree cloned from `main`'s cache needs `lake build RBM3D.Test.Axioms` first (section 2). This is not a defect of the branch.
4. The extra example at L1197 (`W = 1`, `M = 0`) is degenerate but redundant: L1190 is the real instance.

## Verdict
All targets pass: `LocalLawDetSeq`, `FixedTimeFASeq`, `IBPDetSeq`, `LocalLawDetThm`, `FixedTimeFAThm`, `IBPDetThm`, `AvgBoundDetThm`, `LoopFloorThm`, `GavLDetFloorThm`, `GavLDetThm`, `localLawDetThm`, `avgBoundDetThm`, `loopFloorThm`, `gavLDetThm_of_floor`, `gavLDetFloorThm_of_parts`, `gbEXPV3Theorem_of_{gavLDetThm,parts,ports}`, `LocalLaw_gbEXPV3Theorem_of_fa_ibp`, the `_time_zero` lemmas and `LocalLaw_gexRHS_le_maxLoopPM`.

**T2108: PASS.** No repair list. No dispatcher sign-off required.
