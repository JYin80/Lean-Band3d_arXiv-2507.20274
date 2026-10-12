Auditor model: claude-opus-5-5
# T2475 audit (round 1) — Mon Oct 12 23:20:09 UTC 2026

Branch `t/T2475` at 4d8de5b1 (merge base ae791953); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2475-audit1` (detached at 4d8de5b1).
Second scratch worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2475-audit1-main` (detached at current `main` 2dcfcda5, plus untracked copies of the two new files) is used only for §4 (b).
`$S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2475/audit`. Fixed texts: ticket check `docs/tickets/checks/T2475-check.lean` Part 2 (binding) and Part 3 (D1, D2), signed at the 1a-audit (`T2475-1a-audit.md` §9: target 5 = probe `:63`, `:72-82`; target 7 = probe `g1Rowk_of_inputsG_stmt` `:177-191`).

## 1. Statements (script diff, whitespace-normalised, `T2475_` prefix removed from the check)
```
$ python3 -I $S/sdiff.py
RBG_Flow: file:59 ref:165 IDENTICAL 306
RBG_Dom: file:65 ref:170 IDENTICAL 334
RBG_Prod: file:72 ref:175 IDENTICAL 941
RBG_Que: file:87 ref:188 IDENTICAL 1036
RBG_Comp: file:115 ref:256 IDENTICAL 394
RBG_ProfComp vs check ProfComp: file:123 ref:266 IDENTICAL 245
RBG_Comp vs probe: file:115 ref:72 IDENTICAL 394
RBG_ProfComp vs probe: file:123 ref:80 IDENTICAL 245
pad_subseq file:105 probe:63 IDENTICAL
g1Rowk_of_inputsG vs probe stmt: IDENTICAL 787
g1Rowk_of_inputsG vs check D2: IDENTICAL 787
```
Lean-checked equivalences (`$S/eqv.lean`: check Part 2-3 text copied by `sed` from the check file, then 19 `example`s; `lake env lean`, run in the audit worktree):
```
example {d} (K : UNKind d) Ed fT : RBG_Flow K Ed fT ↔ T2475_RBG_Flow K Ed fT := Iff.rfl      -- also Dom, Prod, Que, Comp
example {d} (K : UNKind d) P : RBG_ProfComp K P ↔ T2475_ProfComp K P := Iff.rfl
example : T2475_PadSubseq := RandomLayerBG_pad_subseq
example (d : ℕ) : T2475_FlowGOfBand d := flowG_of_band
example : T2475_g1Rowk_of_inputsG := g1Rowk_of_inputsG
example : T2475_ba_dom_of_bulk := fun d L _ g κ hκ _ hb h0 h1 => ba_dom_of_bulk d L g κ hκ hb h0 h1
example (d : ℕ) : T2475_ba_flowG d := ba_flowG d          -- also ba_domG; ba_mlout as `fun hd h => ba_mlout d hd h`
example (d : ℕ) : BAEd d = T2475_BAEd d := rfl            -- also BAMO = T2475_BAMO
-- Part 4 shapes: target 13 (BA, ProfComp → Comp) := RandomLayerBGBA_comp; band ProfComp ∧ Comp; band Dom; band Prod (identity datum)
$ lake env lean $S/eqv.lean ; echo exit=$?
exit=0
```
D2 binder order (file `:399-413`): `K P ML Loc Que Ed fE fT Fl MO KF PB`, then `RBG_Flow`, `RBG_Dom`, `RBG_Comp`, `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que`, `ML → … RandomLayerB_MLout`, each under `∀ d, 3 ≤ d →`; conclusion the merged `UNG1Rowk K P ML Loc Que` (unchanged; `OUInterfaceK.lean` not in the diff). Same order as the ticket's D2 (Flow′, Dom′, compatibility, Prod′, LL, Que′, MLout).
Mathematical content (ticket targets 6, 10): `ba_flowG` takes `κ' = c = (πκ)^5/2048`, `cT = κ'/(κ'+1)` (leaf `:92-101`); the rows use `τD' = τU/4` (LL, `:265` `RandomLayerBG_oull_seq`) and `τU/2` (Que, `:313`), with the threshold `(4√cT)⁻¹ ≤ N^{τU/4}` resp. `N^{τU/2}` obtained eventually from `Nsz → ∞` (`hA.2.2.1`); eq747 window `ε = min(𝔠(𝔡-𝔡/3), 1)` as merged. All as in the ticket.

## 2. Hidden hypotheses, vacuity, cycles
- No new `structure`/`class`: the new declarations are `Prop`-valued `def`s (`RBG_*`, `BAEd`, `BAMO`, `RandomLayerBG_bandEd`) and theorems; premises appear in signatures only.
- Imports: generic file `RandomLayerB`, `Induction/SizesComp`, `Mathlib.Data.Nat.Nth`; leaf the generic file + merged `BA/UNPins`, `MReg`, `FlowPins`, `MFixedPoint`, `Chain/Carrier`. All merged; no cycle.
- Non-vacuity of the new interface: `RBG_Flow`, `RBG_Dom` are proved at BA (`ba_flowG`, `ba_domG`, hypothesis-free) and at the band; `RBG_Comp` at both (band hypothesis-free; BA from `RBG_ProfComp`); `RBG_Prod`, `RBG_Que`, `RBG_ProfComp` proved at the band from merged discharges. The BA bulk at `S0` is nonempty (`cls_bulk`, used in §3).
- Hypotheses left open (other gates' pins, ticket "Inputs"): `RBG_ProfComp (UNKind.ba d) P` (C3), `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` at BA (C5), `UNMLOutBA` (V3, registered), `UNMLOut`, `UNLocAvgBand`, `UNQueBand`, `UNLocAvgBA`, `UNQueBA` (merged owed pins). `RBG_ProfComp` is an identity of profile values along `sz.comp φ` (no estimate, no limit to check); its band instance is `rfl`. `UNMLOutBA`: the prove report's `v3.py` checks the antecedent at `sz0`/`zSeq` (`t₀ ≥ 2/3`, `Im m ≥ 1/2`, window), and the limit `t₀ → 25/36`; not new in this ticket.

## 3. Compiled nonempty instances (both files build, §4)
- Target 8 (generic, `RandomLayerBG.lean:509`, `RandomLayerBGInst.inst_g1Rowk_of_inputsG`): `g1Rowk_of_inputsG` at the band, `d = 3`, `sz0` (`sz0_admissible`), `𝔠 = 1/6`, `𝔡 = 1/10`, `τU = ouTauMax (1/6) (1/10)` (`ouTauMax_pos`). Every input premise is discharged by a theorem: `RandomLayerBG_flowG_of_band_id RandomLayerB_flow_band`, `RandomLayerBG_dom_band`, `RandomLayerBG_comp_band`, `RandomLayerBG_prod_band`, merged `RandomLayerB_LL_band`, `RandomLayerBG_Que_band`, merged `RandomLayerB_ML_band`. Remaining hypotheses: `UNMLOut`, `UNLocAvgBand`, `UNQueBand` (other gates; as the merged `inst_g1Rowk_of_inputs`). Conclusion `UNOULLk ∧ UNOUEq747k` at `sz0`. Nondegenerate (`N_n = (W L)^3 ≥ 2.1e6`).
- Target 14 (leaf, `d = 3`): `:144` `Flow′` at `S0`, `n = 0`, `z = E_* + i/2`, hypothesis-free; `:151` `Flow′` at `S0`, all `n`, `Im z = N^{-19/20}`, hypothesis-free; `:162` `Dom′` at `S0` (`ε = 1/20`, `η_n = N^{-1+ε}`) and T5 along it at `t ≡ cT` (hypothesis `UNMLOutBA 3`; conclusion `BAFlow … ∧ BAMO …`, not `True`); `:186` `ba_mlout` at `sz0`, `zSeq`, `t ≡ 1/2` (`t0_sz0`); `:191` target 13 at `S0`, `φ = (2 * ·)` (hypotheses `P`, `RBG_ProfComp`); `:201` BA reading of D2 at `S0` (hypotheses C3/C5/V3 pins only). No `N = 0`, no empty index, no collapsed window, no `False` premise.

## 4. Build, axioms, hygiene, diff
(a) Audit worktree (branch 4d8de5b1):
```
$ lake build RBM3D.Universality.GUEPhase.RandomLayerBG RBM3D.BA.RandomLayerBGBA ; echo exit=$?
Build completed successfully (3862 jobs).
exit=0
$ grep -E "warning:.*RandomLayerBG" build.out | grep -v "100 character" | wc -l
0
$ lake build ; echo exit=$?          (full library, runs #assert_rbm_axioms and the registry check)
info: RBM3D.lean:546:0: axiom audit: 13918 theorems, 4412 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4314 jobs).
exit=0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" eqv.out ; grep -c "^#print axioms" eqv.lean
30
30
```
The 30 `#print axioms`: `RBG_Flow/Dom/Prod/Que/Comp/ProfComp`, `RandomLayerBG_pad_subseq`, `RandomLayerBG_Comp_of_law`, `g1Rowk_of_inputsG`, `RandomLayerBG_bandEd`, `RandomLayerBG_flowG_of_band_id`, `flowG_of_band`, `RandomLayerBG_dom_band/_profComp_band/_comp_band/_prod_band/_Que_band`, `RandomLayerBGInst.inst_g1Rowk_of_inputsG`, `BAfT`, `BAfE`, `BAEd`, `BAMO`, `ba_dom_of_bulk`, `ba_Ed_of_im`, `ba_flowG`, `ba_domG`, `ba_mlout`, `RandomLayerBGBA_comp`, `band_terminal`, `bUniv_holds`; every output line is the standard three.
(b) Current `main` 2dcfcda5 (T2477 merged in place `GreenCorr`, `UnivMain`, `Step1Band` after the branch base), scratch worktree:
```
$ lake build RBM3D.Main.BandTerminal RBM3D.Main.BUnivHolds ; echo exit=$?
Build completed successfully (4149 jobs).
exit=0
$ lake env lean $S/bt.lean   (main)  vs  (branch worktree) ; diff
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
IDENTICAL
$ (copy the two new files from t/T2475 into the main scratch tree) lake build RBM3D.Universality.GUEPhase.RandomLayerBG RBM3D.BA.RandomLayerBGBA ; echo exit=$?
Build completed successfully (3862 jobs).
exit=0
```
(c) Hygiene, layering, diff (audit worktree / main repo):
```
$ grep -nE '\bsorry\b|\badmit\b|^\s*axiom|native_decide' <both new files> ; echo grep-exit=$?
grep-exit=1
$ grep -n '^import RBM3D.BA' RBM3D/Universality/GUEPhase/RandomLayerBG.lean ; echo grep-exit=$?
grep-exit=1
$ grep -nE "lemE|lemT|msc|etaT|gueScale|STFlow|2 - κ|BA[A-Za-z]" RandomLayerBG.lean   (split at `section Band`, line 435)
hits before Band: 13  from Band: 19
  before Band: lines 19, 20, 22, 34, 36 (module docstring), 57, 58, 70, 71, 85, 86, 214 (docstrings), 433 (band section doc comment): 0 in code
$ git grep -n "import RBM3D.Universality.GUEPhase.RandomLayerBG\b\|import RBM3D.BA.RandomLayerBGBA" -- 'RBM3D/*.lean' RBM3D.lean
RBM3D.lean:542:import RBM3D.Universality.GUEPhase.RandomLayerBG
RBM3D.lean:543:import RBM3D.BA.RandomLayerBGBA
RBM3D/BA/RandomLayerBGBA.lean:6:import RBM3D.Universality.GUEPhase.RandomLayerBG
$ git diff --name-only main...t/T2475
RBM3D.lean
RBM3D/BA/RandomLayerBGBA.lean
RBM3D/Probe/T2475Pins.lean
RBM3D/Test/Axioms.lean
RBM3D/Universality/GUEPhase/RandomLayerBG.lean
$ git diff main...t/T2475 -- RandomLayerB.lean RandomLayerA.lean OUInterfaceK.lean PinsK.lean RBM3D/Induction | wc -l
       0
$ git diff -U0 main...t/T2475 -- RBM3D/Test/Axioms.lean | grep '^[-+] ' | sed 's/--.*//' | sort | uniq -c ; ... | grep '^@@'
   1 -   `RBM.Univ.UNG1Rowk,
   1 -   `RBM.Univ.UNOULLk,
   1 +   `RBM.Univ.UNG1Rowk,
   1 +   `RBM.Univ.UNOULLk,
@@ -172,2 +172,2 @@ def owedProps : List Name :=
$ git grep -nw <each new public name> main -- 'RBM3D/*.lean' ':!RBM3D/Probe' | wc -l   (main 2dcfcda5)
RBG_Flow=0 RBG_Dom=0 RBG_Prod=0 RBG_Que=0 RBG_Comp=0 RBG_ProfComp=0 g1Rowk_of_inputsG=0 flowG_of_band=0 BAfT=0 BAfE=0 BAEd=0 BAMO=0 ba_dom_of_bulk=0 ba_Ed_of_im=0 ba_flowG=0 ba_domG=0 ba_mlout=0 RandomLayerBGInst=0
```
All five files are sole writable files (the probe is "1a only, never merged"; the hub brings in the other four). `Test/Axioms.lean`: comment text of `:172-173` only (owner text as the ticket); no registry line added; the full build's registry check passes. Unpinned public helpers carry the stems `RandomLayerBG_` / `RandomLayerBGBA_` / namespace `RandomLayerBGInst` (§3 (E)).

## 5. Paper deltas
- `T2449b` (ticket: "lands with this row"): already `docs/paper-deltas.md:1653`, D689 (b) (Flow/Dom/Bulk false at BA; `κ' = (πκ)^5/2048`, `cT`, `η_{t₀} := √fT Im z`; `zztE_BA` condition per D535). Covered.
- Proposed in the prove report (d): `T2475a` (subsequence padding along `Nat.nth` replaces T6), `T2475b` (band datum `RandomLayerBG_bandEd` carries `etaT = √lemT · Im z`, because `RBG_Prod` has no `Im z > 0`), `T2475c` (`Prod′` at `τD' = τU/4`, `τU/2`; rows at `√cT η`). These cover every Lean/paper difference introduced by the two files: `RBG_*` are Lean interfaces with no paper statement (D637 (b)), and `RBG_Comp`/`RBG_ProfComp` are part of `T2475a`.

## 6. Observations (no RETURN)
- O1. `flowG_of_band` (part of target 8) has no `example` of its own in the file; its only premise is the merged theorem `RandomLayerB_flow_band`, and the file's instance applies the stronger `RandomLayerBG_flowG_of_band_id RandomLayerB_flow_band`, from which `flowG_of_band` is derived. The ticket's instance for target 8 is the band `g1Rowk_of_inputsG` instance, which is present.
- O2. Prove report (b) counts 12 generic-part grep hits (split at line 431); this audit counts 13 (split at `section Band`, line 435; the extra hit is the band section's doc comment at 433). All are comments in both counts.
- O3. At BA the scale rows hold only from astronomically large `n` (`log10 N ≥ 3401` at `τU = 1/720`, report (a) table). The statements are `∀ᶠ n`, and no Lean witness uses that `n`. This is the ticket's design (`cT ≈ 2.7e-4`), and the merged band instance has the same form.
- O4. `main` has moved to 2dcfcda5 since the branch base. §4 (b) shows that the two new modules build on it and that `band_terminal`/`bUniv_holds` axioms are unchanged. At merge, `RBM3D.lean` and `Test/Axioms.lean` need the union of lines (H23 (b)): this ticket edits `Test/Axioms.lean:172-173` and T2477 removed 3 lines elsewhere in the same file.

## Verdict
| target | verdict |
|---|---|
| 1-4 `RBG_Flow/Dom/Prod/Que` | PASS (identical to check Part 2; `Iff.rfl`) |
| 5 `RBG_Comp`, `RBG_ProfComp`, `RandomLayerBG_pad_subseq` | PASS (identical to the probe texts signed at the 1a-audit and to check Part 3) |
| 6 repaired rows (private) | PASS (exponents as ticket; used by target 7) |
| 7 `g1Rowk_of_inputsG` | PASS (identical to D2; conclusion merged `UNG1Rowk`) |
| 8 band side + instance | PASS (O1) |
| 9-12 `ba_dom_of_bulk`, `ba_flowG`, `ba_domG`, `ba_mlout` | PASS (inhabit `T2475_ba_*`) |
| 13 `RandomLayerBGBA_comp` | PASS (Part 4 shape) |
| 14 instances | PASS |

T2475: **PASS**. No dispatcher sign-off needed.
