Auditor model: claude-opus-5-5

# T2379 (BA-DT, stage T/U/V design) — audit round 1

Written Sat Oct 10 11:09:48 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2379-audit1`, detached at `t/T2379` = `00a2206` (merge-base with `main` `1f710ee`). Inputs: ticket `docs/tickets/T2379.md`, `docs/reports/T2379-prove.md` (298 lines), `docs/reports/T2379-design.md` (203 lines). Scratch: scratchpad `T2379/audit1/`. Scope per CONTROL H173: design ticket, report-only merge; TV1-TV6 answered with evidence; probe builds; standard axioms; no forbidden tokens.

## 1. Build, axioms, forbidden tokens, diff (probe `RBM3D/Probe/T2379Pins.lean`)
```
$ lake build RBM3D.Probe.T2379Pins   (error/warning lines naming the probe, and the tail)
ℹ [3775/3775] Built RBM3D.Probe.T2379Pins (10s)
info: RBM3D/Probe/T2379Pins.lean:396:0: 'RBM.Ind.loopGenNOf' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2379Pins.lean:397:0: 'RBM.Ind.recovers_loopGenN' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3775 jobs).
$ grep -c "^error" build.log
0
$ lake env lean RBM3D/Probe/T2379Pins.lean; echo exit $?
lake env lean exit 0
$ lake env lean audit1/ax.lean | (#print axioms of the 15 new public declarations) | sort | uniq -c
  15 [propext, Classical.choice, Quot.sound]
$ grep -cwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2379Pins.lean
0
$ wc -l RBM3D/Probe/T2379Pins.lean docs/reports/T2379-design.md docs/reports/T2379-prove.md
     397 RBM3D/Probe/T2379Pins.lean        (limit 400)
     203 docs/reports/T2379-design.md      (limit 400)
     298 docs/reports/T2379-prove.md       (limit 300)
$ git diff --name-only main...t/T2379
RBM3D/Probe/T2379Pins.lean
```
The design report is untracked in the main worktree (`?? docs/reports/T2379-design.md`), as for T2360 (`76106b7` merged `T2360-design.md` from the main worktree). Both sole writable files accounted for; nothing else touched.

## 2. Statements of the probe (statement-centred)
G1 check in the ticket's form (`example : <old> := <old name>`), compiled in `audit1/ax.lean` (no error at these lines):
```
example : type_of% @RBM.Ind.loopGenN := @RBM.Ind.loopGenN
example : type_of% @RBM.Ind.loopGenN := RBM.Ind.recovers_loopGenN
#check @RBM.Ind.loopGenN   (excerpt)
Ind.loopGenN : ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u < 1, ∀ M, M.IsHermitian → ...
  Path.genMat d L W g E u M (Gauss.loopOf σ a) = ↑W ^ d * ∑ ... (zt E u) ... - mSigma E (...) ...
```
- `loopGenNOf` (probe 302-314): `loopGenN` with `zt E` → `ztOf m E`, `mSigma E` → `PropSpin m`, `|E| < 2` → `0 < m.im`; all other hypotheses (`3 ≤ L`, `u < 1`, `M.IsHermitian`, loop `loopOf σ a`) and both cut sums identical. A strict generalisation; the band statement is recovered exactly (`recovers_loopGenN : type_of% @loopGenN`, probe 369-371, `mE_im_pos hE`). `genMat_eq_genMatOf` is `rfl` (probe 296-298).
- Step 2 pins over the carrier (probe 43-64, 78-88): each band pin is recovered by `Iff.rfl` (`bandFM_STAvgU`, `bandFM_STLocalEntryU`, `bandFM_STGdecayW`, `bandFM_STStep2Concl`, `STStep2_iff` against `STStep2` `Step2Defs.lean:599`), so the generic text is definitionally the band text at `bandFM`. `BAStep2` (probe 95-96) uses law `seqP (sz.withLam 0)`, `BAFlow`, `baFMz`, `BAflowT0`, the convention of `BA/FlowPins.lean:555` ("The law of every block Anderson statement of this section is `Sizes.seqP (sz.withLam 0)`").
- Hidden hypotheses / vacuity / cycles: none. No new structure; `FlowFM` is merged (`BA/FlowPins.lean:332`). `BAStep2` is a definition (a pin for later rows), not asserted. No dependency on an unmerged result.

## 3. Compiled nonempty instances (probe 98-104, 379-388)
| endpoint | instance | data | verdict |
|---|---|---|---|
| `loopGenNOf` (band) | probe 380-382 | `d=3, L=3, W=2, g=1/2, m=mE(1/2), E=1/2, u=1/2`, non-scalar Hermitian `LoopGenN_M0`, loop `(+,-,+)` at `(0,1,2)` | nondegenerate, all hypotheses discharged |
| `loopGenNOf` (BA) | probe 385-388 | `sz0`, `n=0` (`L=4, W=32`), `g=0` (the BA kernel), `m=BAmF ...` with `BAmF_sz0_im_pos 0`, `M=1` | nondegenerate; `g=0` is the BA model, not a collapse |
| five `Iff.rfl` bridges | probe 99-102 | `sz0`, `E=0`, `sInst`, `tInst`, `Cd=1`, `d=3` | compiled |
| `recovers_loopGenN` | G1 check itself (`type_of%`) | — | compiled |
```
$ #check @RBM.BA.FlowPinsInst.BAmF_sz0_im_pos
BA.FlowPinsInst.BAmF_sz0_im_pos : ∀ (n : ℕ), 0 < (BA.BAmF Gauss.SizesInst.sz0 (BA.BAflowLam0 ...) (BA.BAflowEs ...) n).im
$ sed -n 38,40p RBM3D/Defs/Block.lean      (g = 0 gives sbKernel = 1_{x=0})
noncomputable def sbKernel : Zd d L → ℂ := fun x =>
  if x = 0 then ((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ)
  else if zdistD d L x = 1 then ((g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ)
```

## 4. TV1 measurement reproduced
```
$ sed -n 55,622p RBM3D/Induction/LoopGenN.lean > merged_55_622.txt; cmp lg/merged_block.txt merged_55_622.txt
merged_block = LoopGenN.lean:55-622
$ git diff --no-index --numstat lg/merged_block.txt lg/gen_block.txt
136	99	merged_block.txt => gen_block.txt                 (g = 136/568 = 0.239)
$ python3 -I (provenance of every non-blank line of gen_block.txt)
gen_block nonblank 542 in probe 257 in merged 430 in neither 1
  |           loopL d L W (blockMat d L W M) (zt E u) ((loopOf σ a).cutGlue k' y) :=
```
(the one line in neither is the band corollary's statement, kept). Model arithmetic (chain = ((1-f)·S·g + f·S·0.8 + 6,720 + 4,320 + 3,800)/1000, S = 95,029) checked by hand against B9a: at `(g,f)=(0.239,0)`: 22,712 + 14,840 = 37.6; corner `(0.5,0.30)`: 33,260 + 22,807 + 14,840 = 70.9; break-even at f=0: (84,700−14,840)/95,029 = 0.735. All match the report. Row arithmetic: ST 10+11+3 = 24, BA 8+8+2+3 = 21, +row 0 = 46; sub-stages 19/19/8 (flags 28.5/28.5/12.0) match.

## 5. File:line evidence spot-checked (29 TV3 citations + 30 TV2/TV6 citations)
```
$ bash -c 'for x in "<file> <line> <name>" ...; sed -n "$2p" $1.lean | grep -q "$3"' | summary
29 ok, 0 MISS  (DecayLoopA:775, DecayLoopB:1444/2006/2213, Step2Events:1296/1370, Step2Iterate:1243, EMn2Exp2:725/942,
  NewKLK:697/996, AzumaProxyN:503, GridDriftN:519, HierAlgebra:485, NewPQ:639, QopNorm:384, B45:1560,
  Step34Pins:534/595/656, IniTermI:2008, EtermsMid:1212, Step5Pins:88, Step6Pins:331, Step6Kit:190/329/571,
  NQEndFlowLift:477, OptL2a:404)
$ sed -n <line>p (TV2/TV6 citations)
BA/FlowPins.lean:7-8 import Induction.Defs, Induction.Step2Defs | :328 def PrecL | :332 structure FlowFM | :458 def STEEg
  | :490 theorem bandFM_STLK | :565 def STMainIndG | :1422 theorem BAmF_sz0_im_pos
MainIndOut.lean:51 def STMLOutG | :99 stMLOutG_of_mainIndG | :144 unMLOutBA_of_pins ; MainIndBase.lean:50 STLK0 ; MainIndChain.lean:43 STHorizonG
Step4.lean:209 ST_mainInd_of_pins' | :213 STStep1 ; Step34Pins.lean:221 STStep2Concl | :250 STStep3R ; Step5Pins:101 STStep5R ; Step6Pins:126 STStep6R
Step1Fam.lean:361 BAStep1 | :695 baStep1_holds (BAGbEXPii → BAGbEXPij → BAStep1) | :982 inst_baStep1 ; Step1Boot.lean:108 BAGbEXPii | :116 BAGbEXPij
MainIndRegimes.lean:165 ST_mainIndR_of_steps | :616 ST_mainInd_of_regimes ; NQEndFlowLift.lean:581 stKloop_lip ; BA/KKernel.lean:124 BAK_row_sum
Step2Defs.lean:7 import Induction.Step34Pins (L1 confirmed: FlowPins → Step2Defs → Step34Pins) ; :406 STLWB | :421 STLWT | :456 STEMn2Exp
Generator.lean:725 Generator_hasDerivAt_ztOf ; Path/OneStep.lean:68 genMat ; Loop/GLoopFlow.lean:55 ztOf ; Propagator/Pins.lean:30 PropSpin
Defs/Block.lean:36 (blank; sbKernel is at :38)                         -> observation O1
$ grep -rc "^open private" RBM3D/Induction | grep -v ":0"
Induction/DuhamelII.lean:2   Induction/EMn2Exp2.lean:5               (7 statements in 2 files, as stated)
$ grep -rn STKwardgL RBM3D | wc -l
0
$ sed -n 160p docs/supervisor/2026-10-10-0853.md   (excerpt)
Total 6108 net lines against 5339 design central, **1.14×**.
$ sed -n 1841,1842p paper/tex/7_8_light_weight.tex   (excerpt)
%The proof of \Cref{lem:main_ind_BA} follows the same six-step strategy ... We now describe how the arguments ...
The proof of \Cref{lem:main_ind_BA} follows the same six-step strategy ... We now explain how the arguments ...   -> O2
$ grep -rln "import RBM3D.BA.FlowPins" RBM3D/Induction RBM3D/Evolution RBM3D/Path
RBM3D/Induction/MainIndBase.lean                                        -> O3
```

## 6. Per question (design ticket targets)
| item | evidence | verdict |
|---|---|---|
| TV1 route / tripwire | measured block `LoopGenN.lean:55-622` (one of the three allowed), g = 0.239 reproduced (§4), f_sem = 0 by construction (band instance 3 lines, BA instance the same theorem); G1 kept (§2); break-even and corner reproduced | PASS |
| TV2 carriers and pins | 15 carriers in the ticket's order (T8, T7, T1, T2, T3, ..., V1, V2/V3); existing generic pins cited and verified (§5); new Step 2 family compiled with `Iff.rfl` bridges; BA readings listed per carrier; L1 layering finding verified (`Step2Defs.lean:7`) | PASS |
| TV3 dependencies | K / E / L / G / C columns per row with 29 verified `file:line`; start-now vs stage-close split stated (§3 of design) | PASS |
| TV4 row table | ST and BA rows with lo / central / hi, pairing, roles, cone and certificate cost; first tickets row 0 and T5s1 (the tripwire block) | PASS |
| TV5 count and flag | 40.6 [30.6, 57.0] (46.4 with 1.144) vs pilot 38.9 [37.5, 48.3]; route I/T 84.7 / 98.9; 46 rows > 40 → sub-stages T/U/V with flags; BA ticket 46 | PASS |
| TV6 band side | 96 of 101 files, 203 frozen declarations in 42 files (G1), certificate cones (20 files, 12 tickets), measured rebuild times, `open private` coupling verified, no `Graph/`/`LW*` edits; G2 addressed | PASS |
| probe | builds, `lake env lean` exit 0, 15 × standard axioms, 0 forbidden tokens, ≤ 400 lines, instances nondegenerate | PASS |
| paper deltas | `T2379a` (`loopGenNOf` generic in `m`, `g`; BA case not stated by the paper) and `T2379b` (`BAStep2` as Lean's reading of `7_8:1825-1841`) proposed in design §7 and prove (d); no other Lean/paper statement difference in the probe | PASS |

## 7. Observations (no statement, instance, build, axiom or paper-delta effect)
- O1. `Defs/Block.lean:36` is cited for `sbKernel`; the definition is at `:38` (36 blank, 37 docstring).
- O2. The paper quote is cited at `7_8:1841`; that line is commented out ("describe"); the live sentence ("explain") is `:1842`.
- O3. Design §2 L1: "no chain file imports `BA/FlowPins` today". True for the 101-file list; `Induction/MainIndBase.lean` (the main-induction group, counted separately as already generic over `FlowFM`, `common.py` `NEW_V2`) does import it. L1's conclusion (`Step2Defs`, `Step34Pins` upstream of `FlowFM`) is unaffected.
- O4. For the supervisor's opening REQ (not a defect): the tripwire was run on `LoopGenN`, the allowed block with the least class-(t) content; the design itself reports `KDecay` at 31% class-(t) lines (read, not compiled, above the 0.30 line) and proposes the second tripwire at T5s2 (`HierAlgebra`) and U2 (`KDecay`). The chain-level break-even f at g = 0.24 is 0.884 (B9a), so the route recommendation does not depend on it.
- O5. Process note: the auditor's first build log was written to scratchpad `T2379/build.log` (overwriting the prover's scratch log of the same name) and then moved to `T2379/audit1/`; no report block cites that file.

## Verdict
**PASS** (design report-only; probe stays on `t/T2379`). No dispatcher sign-off requested by this audit; the design's own §7 decisions go to the supervisor as the opening REQ of stage T/U/V.
