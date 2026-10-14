Auditor model: claude-opus-5-5
# T2501 row a1 audit (`RBM3D/BA/Step5KerBA.lean`), round 1 — 2026-10-14 03:19:52 UTC
Branch `t/T2501` at 0d98bc2b; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2501-audit1` (detached). Scope: targets 1, 3, 4, 5, 6, 7 and their instances in 8 (row a1 only; target 2 is row a2, targets 9-12 are row b).

## 1. Statement vs pin (script diff, then a compiled equality check)
```
$ python3 -I sdiff.py docs/tickets/checks/T2501-check.lean RBM3D/BA/Step5KerBA.lean   (whitespace-normalised text of `def T2501_X : Prop :=` vs `theorem name :`)
T2501_KerFactsBA vs baIniTermGen_kerFacts: IDENTICAL
T2501_ThDecayBA vs baStep5KerGen_thDecay: IDENTICAL
T2501_NewKLKLBA vs baEtermsMid_newKLKL: IDENTICAL
T2501_FlowModBA vs baLemDecCalELipG_flowMod: IDENTICAL
T2501_KLipBA vs baKLip_two: IDENTICAL
T2501_NewKLKLgLBA vs baNewKLKLgL': IDENTICAL
$ lake env lean audit_pins.lean   (check lines 1-275 + `import RBM3D.BA.Step5KerBA`, then `example : T2501_X := name` for the six pins, then #print axioms)
exit 0
'RBM.BA.baIniTermGen_kerFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5KerGen_thDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEtermsMid_newKLKL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLemDecCalELipG_flowMod' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKLip_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baNewKLKLgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Ticket mathematics: `∃ C₆` after `κ` in `baStep5KerGen_thDecay` (ticket decision (11), T2498 Amend 1): yes (`∀ κ 𝔡 … → ∃ C₆`). `∀ d, 3 ≤ d` (decision (7)): every target carries `3 ≤ d` (directly or inside the merged class `IniTermGen_KerFacts` / `EtermsMid_NewKLKL` / `STNewKLKLgL'`); `baLemDecCalELipG_flowMod` is `∀ d` with no `3 ≤ d`, as pinned. Constants before `(sz, z)`: in each statement the `∃` precedes `∀ sz` (pins identical). The classes read are merged definitions (`IniTermIIGen:68`, `Step5KerGen:188`, `EtermsMid2:46,56`, `LemDecCalELip:311`, `NQEndFlowGen:209`, `Step5Gen:164`); their bodies were read: all windows/guards are explicit binders (`0 < gK n → gK n ≤ Λ`, `0 ≤ t → t < 1`, `∀ᶠ n`), no hidden structure field.

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE '^(noncomputable )?(def|abbrev|structure|class|instance) ' RBM3D/BA/Step5KerBA.lean | wc -l
       0
$ grep -nE '^(theorem|lemma) ' (public declarations)
132:theorem baStep5KerGen_thDecay   161:theorem baIniTermGen_kerFacts   361:theorem baEtermsMid_newKLKL
390:theorem baLemDecCalELipG_flowMod   476:theorem baKLip_two   550:theorem baNewKLKLgL'
$ private decls without stem Step5KerBA_ : (none)
$ C1 grep (BAK_le_small|BAMB_upper_small|Mbound_AO|W^(-eps|BAm_im_lower_window||E||norm_mE|mSigma|SB d|E2Hyp|STGridRepNgL) | wc -l
       0
$ grep -c 'T24[0-9][0-9]_'  ->  0
$ grep -rln 'import RBM3D.BA.Step5KerBA' RBM3D RBM3D.lean
RBM3D.lean
$ grep -n '^open private'
61:open private nkl_zdistInf_sub_comm from RBM3D.Induction.NewKLK
62:open private NewKLKBA_tail from RBM3D.BA.NewKLKBA
63:open private Step2IterBA_lam_window from RBM3D.BA.Step2IterBA
64:open private newKLKL_Cs_ge_one newKLKL_tailT_le_tailW from RBM3D.Induction.NewKLKL
65:open private NewKLKGen_ward_LKM from RBM3D.Chain.NewKLKGen
66:open private NewKLKLGen_bound2 from RBM3D.Chain.NewKLKLGen
```
- No new `def`/`structure`; the only flow predicate is the merged `BAFlow`; no target has a premise beyond its pin (pins identical, §1).
- No cycle: the 13 imports are merged modules (`Chain/*`, `Induction/EtermsMid2`, `BA/*`); the new module has no importer besides `RBM3D.lean`.
- External hypotheses: none (row a1 takes no external input; every premise is a merged result or a binder of the pinned class).
- `open private` reads merged private lemmas without editing their files (diff §4 is empty outside the new file); the ticket names `NewKLKBA_tail`, `NewKLKLGen_bound2`, `NewKLKGen_ward_LKM`, `newKLKL_tailT_le_tailW` by `open private`. No stop rule is triggered.

## 3. Compiled nonempty instances (section 6 of the file, lines 555-705; compiled by the module build in §4)
Concrete data: `d = 3`, merged `sz0`, `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`, a theorem), `half_lt_t0` (`FlowPins:1254`). None of the seven `example`s has a binder or an open hypothesis.
| target | instance (line) | data | deterministic premises discharged |
|---|---|---|---|
| `baIniTermGen_kerFacts` | 585 | `n = 0` (`L = 4`, `W = 32`), `t = 1/2`, both σ, all `a b` | window `0 < g₀_0 ≤ 10` by private `Step5KerBA_inst_window` (every `n`, from `baStep2Fam_lam_pos_le`, `lam_n ≤ 1`); `0 ≤ 1/2 < 1` |
| `baStep5KerGen_thDecay` | 605 | class at `(sz0, zSeq)` + entry bound at `n = 0`, `t = 1/2` | same window; `t` range |
| `baEtermsMid_newKLKL` | 616 | eventual class + at some `n`: `u = 0`, `D = 1`, `H = g₀Ψ` | `H` Hermitian (`Step5KerBA_inst_herm`); `‖G−M‖ ≤ δ₀` proved via `G_0 − M = 0` (not a `False` premise) |
| `baLemDecCalELipG_flowMod` | 646 | `(κ, ε, 𝔡) = (1/2, 1/10, 1/10)`, `sz0`, `zSeq` | `0 < κ, ε, 𝔡`; `flow_sz0` |
| `baKLip_two` | 653 | `t ≡ 1/2 ≤ t₀_n`; at some `n`: `u = 0`, `u' = 1/2` | `half_lt_t0`; `0 ≤ u ≤ t`, `0 ≤ u' ≤ t` |
| inline `hmn`, `hSr` (target 6) | 662 | every `n`, `a` | `flow_sz0` |
| `baNewKLKLgL'` | 668 | size sequence `sz0.withLam g₀`, `n = 0`, `E = E₀`, `u = 0`, `D = 1`, `H = g₀Ψ` | window at `n = 0`; `1/2 ≤ Im m` (`EMn2BA_mF_data`); Hermitian; `‖G−M‖ = 0 ≤ δ₀` |
Nondegenerate: `L_0 = 4` (64 sites, `d = 3`), `W_0 = 32`, `N_0 = 2097152`, `g₀_0 > 0` proved; no `N = 0`, empty index, collapsed window or astronomically large witness. The `∃ n` in the A9 and D3 instances comes from `Filter.Eventually.exists` on `atTop` (nonempty), applied to non-trivial `u, u', H`.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.Step5KerBA   (audit worktree)
✔ [4112/4112] Built RBM3D.BA.Step5KerBA (16s)
Build completed successfully (4112 jobs).
exit 0
$ grep -c '^error' build.out  ->  0 ; lines mentioning Step5KerBA: only the ✔ line above (no warning)
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' RBM3D/BA/Step5KerBA.lean
0
$ git diff --stat main...HEAD
 RBM3D.lean               |   1 +
 RBM3D/BA/Step5KerBA.lean | 708 +++++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 709 insertions(+)
$ git diff main...HEAD -- RBM3D.lean | grep '^[+-][^+-]'
+import RBM3D.BA.Step5KerBA
$ git diff main...HEAD -- RBM3D/Test RBM3D/Chain RBM3D/Induction RBM3D/Evolution RBM3D/Graph | wc -l
       0
```
Axioms of all six targets: the standard three (§1). Touched files = the row-a1 sole writable files (`RBM3D/BA/Step5KerBA.lean` new, `RBM3D.lean` import line); no `Test/Axioms.lean` edit (ticket: row a1 none). No frozen signature touched (no merged file changed). Size 708 lines < row-a1 stop line 1,150. The full `lake build` is the hub's at merge.

## 5. Paper deltas
- The six statements equal their pins; the pins are the merged generic classes at the BA tuple. The only Lean-side shape choice the ticket flags, `∃ C₆` after `κ` (BA tail constant `Q₀(d, Λ, κ)`), is proposed in the prove report as candidate `T2501a` (§(d)); `docs/paper-deltas.md` has no T2501 entry yet (`grep -n T2501` -> 0), so the candidate is the coverage. No further Lean/paper difference found (A9 does not read F7; R1 enters only as the KerFacts conjunct, the pinned class text).

## Verdicts
- `baIniTermGen_kerFacts` (T2501_KerFactsBA): **PASS**
- `baStep5KerGen_thDecay` (T2501_ThDecayBA): **PASS**
- `baEtermsMid_newKLKL` (T2501_NewKLKLBA, A9): **PASS**
- `baLemDecCalELipG_flowMod` (T2501_FlowModBA, D2): **PASS**
- `baKLip_two` (T2501_KLipBA, D3): **PASS**
- inline `Step5KerBA_hmn`, `Step5KerBA_hSr` (target 6, private): **PASS**
- `baNewKLKLgL'` (T2501_NewKLKLgLBA): **PASS**
**Row a1 overall: PASS.** No dispatcher sign-off needed.

## Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The prove report is 212 lines; the ticket's acceptance line asks ≤ 150 (CLAUDE.md §6 allows 300).
- O2. Imports: `Induction/EtermsMid2` in place of the ticket's `Induction/EtermsMid` (the ticket lets the 1a fix the lists; `EtermsMid2` defines `EtermsMid_NewKLKL`).
- O3. Three `open private` names beyond those the ticket names (`nkl_zdistInf_sub_comm`, `Step2IterBA_lam_window`, `newKLKL_Cs_ge_one`); read-only use, no merged file changed.
- O4. Section (a) cites `BAMB_shift` for the shift; the proof uses `baP8_BATheta_shift` (`Prop6Path:497`) instead (stated in the report's narrative).
- O5. Report (d) doc finding on `EMn2BA_mF_data`'s docstring (`‖m_F‖ ≤ 1` vs `Im m_F ≤ 1`) is for the dispatcher; it does not affect this file.
