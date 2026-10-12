Auditor model: claude-opus-5-5

# T2467 audit, round 1 (Mon Oct 12 21:16:00 UTC 2026)

Inputs: ticket `docs/tickets/T2467.md`, Amend 1 (`T2467-amend-1.md`, CONTROL H255 (3)), CONTROL H256 (4) (UN-C4: the stop-rule literal reads as R1),
check `docs/tickets/checks/T2467-check.lean`, prove report `docs/reports/T2467-prove.md`, branch `t/T2467` at 12f4da0a.
Audit worktree `RBM3D-wt/T2467-audit1` (detached at 12f4da0a). Scratch: `scratchpad/T2467/auditor1/Aud.lean` (not committed).

## 1. Diff, layout, frozen files (Amend 1)
```
$ git diff --stat main...t/T2467
 RBM3D.lean                        |    2 +
 RBM3D/Chain/Step2EventsGen.lean   | 1351 +++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/Step2EventsGenTw.lean |  171 +++++
 RBM3D/Test/Axioms.lean            |    6 +
 4 files changed, 1530 insertions(+)
$ git diff main...t/T2467 -- RBM3D/Chain/DecayGenTw.lean RBM3D/Induction/ RBM3D/BA/ RBM3D/Chain/{Step2Gen,DecayGen,LWGen,Carrier}.lean | wc -l
       0
$ git diff main...t/T2467 | grep -c '^-[^-]'          # deleted lines anywhere
0
$ git diff main...t/T2467 -- RBM3D.lean               # two import lines before `#assert_rbm_axioms`
+import RBM3D.Chain.Step2EventsGen
+import RBM3D.Chain.Step2EventsGenTw
$ wc -l RBM3D/Chain/Step2EventsGen.lean RBM3D/Chain/Step2EventsGenTw.lean    # stop line 2,000; reserve B unused (< 1,800)
    1351 RBM3D/Chain/Step2EventsGen.lean
     171 RBM3D/Chain/Step2EventsGenTw.lean
$ grep -n '^import RBM3D.BA' RBM3D/Chain/Step2EventsGen.lean ; echo exit $?
exit 1
$ closure of RBM3D.Chain.Step2EventsGen over `^import RBM3D.` lines (python)
RBM3D.Chain.Step2EventsGen closure 99 BA 0 forbidden []        # forbidden = Step2Iterate|OptL2*|LWTermHolds|LWExpCert*
$ grep -rln "import RBM3D.Chain.Step2EventsGen\|import RBM3D.Chain.DecayGenTw" RBM3D RBM3D.lean
RBM3D/Chain/Step2EventsGenTw.lean
RBM3D.lean
```
Sole writable files under Amend 1 (item 5): exactly these four. `DecayGenTw.lean` untouched; the leaf has the single importer `RBM3D.lean`.

## 2. Statements against the pins (script: the check file's Part 2 + auditor examples, compiled on the branch)
`Aud.lean` = check-file imports + `Chain.Step2EventsGen`, `Chain.Step2EventsGenTw` + check-file lines 153-373 (all `T2467_*` pins, verbatim)
+ the following (each compiled):
- `Iff.rfl` for `STScaleInvgL`, `STBdatagL`, `STEvWeakg`, `STEvInitg`, `STEvLWg`, `STEvMGg` against `T2467_ScaleInvgL`, `T2467_BdatagL`, `T2467_Ev*`,
  and `Step2EventsGen_Grid`, `Step2EventsGen_Rot3`, `Step2EventsGen_Flow` against `T2467_Grid`, `T2467_Rot3`, `T2467_Flow` (9 of 9).
- `aud_good_iff : STGoodAtg … ↔ T2467_GoodAtFields …` by `⟨fun h => ⟨h.weak, h.init, h.lw, h.mg, h.mart, h.rem, h.ident⟩, fun ⟨h1,…,h7⟩ => ⟨h1,…,h7⟩⟩`
  (field by field, in order).
- `example (d law Flow mk T0) : T2467_X d law Flow mk T0 := X d law Flow mk T0` for `ST_LW_sectionsg`, `ST_event_lwg`, `ST_event_mgg`;
  `example : T2467_ST_event_weakg := ST_event_weakg`, same for `ST_event_initg`; `stLWBgL_of_LWtermG`, `stLWTgL_of_LWtermExpG` with
  `(d law Flow T0 mkF)` (7 of 7, no binder change, no premise dropped).
- `example : T2467_ST_good_probg` from `ST_good_probg` with the same 30 binders, then `congr 1; ext ω; simp only [Set.mem_setOf_eq, aud_good_iff]`.
- check-file shapes proved: `bandFM_STScaleInv`, `bandFM_STBdata` (`Iff.rfl`), F7/F9 at band (`Step2EventsGen_bandRot3`, `_bandGrid`), F1-F2 at band
  (`_bandFlow`), F7/F9 at BA (`Step2EventsGenTw_baRot3`, `_baGrid`, law `seqP (sz.withLam 0)`), F1-F2 at BA (`_baFlow`), and the band reading
  `STGoodAt sz … ↔ T2467_GoodAtFields (bandStep2Mat sz Es) …` via `Step2EventsGen_bandGoodAt` + `aud_good_iff`.
```
$ cd RBM3D-wt/T2467-audit1 && lake env lean $SP/Aud.lean ; echo exit $?
Aud.lean:270:29: warning: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
exit 0
$ lake env lean docs/tickets/checks/T2467-check.lean 2>&1 | grep error ; echo check-exit ${pipestatus[1]}
check-exit 0
```
Quantifier order, losses and ranges follow the pin text exactly (definitional equality checked by Lean): `Dm` premise `D' + 1 + 3 ≤ Dm`,
`hcardLab` `N^3`, (E3) `Λ ≥ N^{ε₁}`, (E4) `Λ ≥ 2N^{ε₁}`, `Cm.eta` in place of `(mE E).im (1 - u)`, the `Ĵ` form, `STgDriftg` in `ident`.
Unprefixed public names (all pinned): `STScaleInvgL bandFM_STScaleInv ST_LW_sectionsg STEv{Weak,Init,LW,MG}g ST_event_{weak,init,lw,mg}g STGoodAtg
ST_good_probg STBdatagL bandFM_STBdata stLWBgL_of_LWtermG stLWTgL_of_LWtermExpG`; every other public name has stem `Step2EventsGen_`/`Step2EventsGenTw_`.

## 3. Hidden hypotheses, vacuity, cycles, hypothesis rules
- No new structure carries a hypothesis: `STGoodAtg` is the pinned event (a conclusion of `ST_good_probg`, never a premise of a target);
  `FlowFM`/`Step2Mat` are unchanged (diff in §1). F1-F2, F7, F9 are explicit `Prop` premises, each concluded at band and BA by theorems here.
- Other-gate inputs stay hypotheses only: `STLWTgL`, `STEMn2ExpgL`, `STStep1WeakgL`, `STScaleInvgL`, `STDecaygL`, `LWtermG`, `LWtermExpG`, (E5), identity, remainder.
  No cycle: `Step2EventsGen` imports only merged modules (closure §1, no `Step2Iterate`); none of these inputs is concluded from a T2467 result.
- X1-C1 spectral grep on `Step2EventsGen.lean`, each hit classified by line (comment / `bandFM_*` bridge lines 442-443, 974-976 / band facts 1116-1172 / section Instances ≥1173):
```
comment 12 [33, 34, 78, 79, 580, 811, 1115, 1120, 1124, 1129, 1137, 1243]
bandbridge 2 [443, 975]
bandfact 9 [1117, 1118, 1126, 1127, 1132, 1133, 1143, 1144, 1145]
instance 57
$ grep -nE 'withLam|lam0|BAflowLam0|seqHflowBA|gK|g₀' RBM3D/Chain/Step2EventsGen.lean ; echo exit $?
exit 1
$ grep -cE 'gK|g₀' RBM3D/Chain/Step2EventsGenTw.lean
0
$ grep -nE 'sorry|admit|native_decide|^axiom|^ *axiom ' RBM3D/Chain/Step2EventsGen*.lean ; echo exit $?
exit 1
```
  No generic statement or proof line hits (0 `OTHER`). UBA-C1 / UN-C4 (R1 literal): not triggered, no `gK`/`g₀` anywhere. The leaf's `withLam`/`BAflowLam0`/`seqHflowBA`
  hits are the BA carrier shapes the check file itself pins (`T2467-check.lean:399-412`); the ticket's glob `Step2EventsGen*.lean` predates Amend 1 (observation O1).

## 4. Compiled nonempty instances (endpoint theorems)
Concrete data `d = 3`, `sz0`, `z0`, `flow_z0`, `[s, T] = [sInst, tInst] = [0, 1/16]`, `K = KI ≡ 16` (`KI_ne`), carrier `bandStep2Mat sz0 (STflowE z0)`:
| target | site | deterministic premises discharged | left open (other gates) |
|---|---|---|---|
| `ST_LW_sectionsg` | Gen:1185 | F1-F2 `Step2EventsGen_bandFlow 3`, `0<3`, κ=ε=𝔡=1/10, 𝔠=1/6, `flow_z0`, `sI_nonneg`, `sixteenth_le_lemT`, `cB=1/2,c=1/4`, `hBd_sz0`, `hKcap_sz0` (Kf≡0), section `tt n = sInst n` | `bandPin STLWTgL 3`, `bandPin STEMn2ExpgL 3`, `STStep1WeakgL`, `STScaleInvgL` |
| `ST_event_weakg` | Gen:1195 | F9 `bandGrid`, `C₁=5` `hcard_idx`, `ε₁=1/8`, `δ₀=3` `hsmall_sz0` | `STStep1WeakgL` |
| `ST_event_initg` | Gen:1202 | F9, `C₁=3` `ST_card_lab_le`, `Di=24`, `D=1`, `a₀=2N^{1/8}Bctl^{1/5}` with `ST_init_cmp` | `STDecaygL` |
| `ST_event_lwg` | Gen:1216 | as row 1 + F3 `DecayGen_bandSpec` (κm=√(1/10)/2), F9, `C₁=4` `hcard_lab`, `Λ=N^{1/8}`, `D=1` | as row 1 |
| `ST_event_mgg` | Gen:1230 | as row 4 with `C₁=5` `hcard_fin2lab`, `Λ=2N^{1/8}` | as row 1 |
| `ST_good_probg` | Gen:1246 | `Sizes.tendsto_size sz0`, `hΔ` `ST_gridStep_nonneg`, `D'=1, Dm=5` (= D'+4), `ε₁=1/10`, `Λ=N^{1/10}` (`hΛ` le_rfl), `hρ` (ρ₁≡1, `ST_prof_lower_N`), `hcardLab` | (E1)-(E4), (E5) tail, identity, remainder |
| `stLWBgL_of_LWtermG` | Gen:1292; Tw:158 closed | `3≤3`, F1 `h.1`, F7 `bandRot3`; Tw:158 `Step2EventsGenTw_band_STLWBgL` closed by `band_LWtermG` | Gen:1292 `bandPin LWtermG 3`; none at Tw:158 |
| `stLWTgL_of_LWtermExpG` | Gen:1297; Tw:164 closed | same; Tw:164 closed by `band_LWtermExpG` | none at Tw:164 |
BA-family applications (Tw:94 (E3), Tw:113 (E4), Tw:132 (E1), Tw:144/148 target 11) discharge F1-F2, F3 (`EMn2BA_mF_data`), F7, F9 at BA and `baSTEMn2Exp`;
they are generic in `sz, z` (supplementary: the concrete instances are the band rows above). No `N = 0`, empty index, collapsed window or `False` premise:
`1/16 > 0`, `KI ≡ 16 ≠ 0`, `STLab sz0 n` nonempty; the preflight script (prove report (a)(ii)) checks every arithmetic premise from `n = 0` (`N ≥ 2.1e6`).
All instance blocks compile in the module build (§5).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Chain.Step2EventsGen RBM3D.Chain.Step2EventsGenTw 2>&1 | grep -E "error|declaration uses|Build completed"
Build completed successfully (3999 jobs).
$ lake build 2>&1 | grep -E "error|unregistered|Build completed" | tail -2      # registry pre-check: root import + #assert_rbm_axioms + premise scan
Build completed successfully (4306 jobs).
$ #print axioms (in Aud.lean)
'RBM.BA.ST_LW_sectionsg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ST_event_weakg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ST_event_initg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ST_event_lwg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ST_event_mgg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ST_good_probg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stLWBgL_of_LWtermG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stLWTgL_of_LWtermExpG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STScaleInv' / 'bandFM_STBdata' / 'Step2EventsGen_bandGoodAt' / '_bandGrid' / '_bandFlow' / '_bandRot3' /
'Step2EventsGenTw_baGrid' / '_baFlow' / '_baRot3' / '_band_STLWBgL' / '_band_STLWTgL': each [propext, Classical.choice, Quot.sound]
```
Registry (`Test/Axioms.lean`, diff): 5 `owedProps` lines + 1 comment line: `STScaleInvgL` (T1 / T1-BA), `STDecaygL` (main induction / BA-V),
`LWtermG`, `LWtermExpG` (BA-L6), `STGoodAtg` (T1's P4; found by the scan through its field projections). The full build passes the
unregistered-premise check with them. Nothing else in the file changed.

## 6. Paper deltas
Lean/paper statement differences of this row: (a) F7 (3-loop trace cyclicity) explicit premise of the two L-bridges; (b) F9 (model matrix and the
law (5.1) of the grid state) explicit premise of (E1)-(E4); (c) (E3)/(E4) read `Cm.eta` and `DecayGen_Spec` (`κm ≤ Im m`) instead of `|E| ≤ 2 − κ`,
`(mE E).im (1 − u)`; (d) the carrier substitution itself (`FlowFM`/`Step2Mat` for band objects). (a), (b) are proposed in the prove report (d)
as `T2454a`, `T2454b`; (c) is `T2454c` (T2454-prove `:128`); all three are listed as pending candidates in `docs/paper-deltas.md:1598`
("T2454a–d … numbered when the row merges"); (d) is D660's pattern (`paper-deltas.md:1624`). `Dm = D' + 4` and the `Ĵ` form are the band's. Coverage complete.

## 7. Observations (no RETURN)
- O1: the ticket's `Step2EventsGen*.lean` globs (X1-C1 second grep, `^import RBM3D.BA`) predate Amend 1 and match the BA leaf; read on `Step2EventsGen.lean`
  (above), the leaf's hits are the pinned BA shapes. Dispatcher may tighten the glob in later tickets.
- O2: the prove report proposes its candidates under the tags `T2454a/b` rather than `T2467a`; they are the tracked T2454 candidates, so coverage is unaffected.
- O3: prove report (a′) says the instances use the (a) data (row 8 `Λ = 2N^{1/8}`, `ε₁ = 1/8`); the compiled target-10 example uses `Λ = N^{1/10}`, `ε₁ = 1/10`
  (its docstring agrees with the code); the instance is nondegenerate either way.
- O4: `Set.mem_setOf_eq` deprecation warning (Mathlib), no effect.

## Verdict
| target | verdict |
|---|---|
| 8 `STScaleInvgL`, `bandFM_STScaleInv`, `ST_LW_sectionsg` | PASS |
| 9 `STEv{Weak,Init,LW,MG}g`, `ST_event_{weak,init,lw,mg}g` | PASS |
| 10 `STGoodAtg`, `ST_good_probg` | PASS |
| 11 `STBdatagL`, `bandFM_STBdata`, `stLWBgL_of_LWtermG`, `stLWTgL_of_LWtermExpG` | PASS |
| carrier facts F1-F2, F7, F9 (band, BA), layout under Amend 1 | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
