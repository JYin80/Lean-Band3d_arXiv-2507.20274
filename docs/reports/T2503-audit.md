Auditor model: claude-opus-5-5

# T2503 audit (round 1) — V2a design gate: report `docs/reports/T2503-design.md` + probe `RBM3D/Probe/T2503Pins.lean`
Branch `t/T2503` at 93bd54cd (merge-base with `main` 6b359e50); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2503-audit1` (detached).
Scripts and outputs: scratchpad `T2503/audit1/` (`cmt.py`, `tokdiff.py`, `price.py`, `v1.py`, `iffrfl.lean`, `neg.lean`, `ax.lean`).

## 1. Diff scope (sole writable files) and comment-only edits
```
$ git diff --stat main...t/T2503
 RBM3D/BA/LWPinsBA.lean       |   8 +-
 RBM3D/BA/Step2CloseBA.lean   |   2 +-
 RBM3D/BA/TwistPins.lean      |   4 +-
 RBM3D/Graph/BAGGExp.lean     |   2 +-
 RBM3D/Probe/T2503Pins.lean   | 391 +++++++++++++++++++++++++++++++++++++++++++
 docs/reports/T2503-design.md | 179 ++++++++++++++++++++
 6 files changed, 578 insertions(+), 8 deletions(-)
$ git diff --stat 6b359e50 main -- <the four commented files> RBM3D/Probe     # main moved 1 commit (22bbe858, docs only)
(empty)
$ grep -c Probe RBM3D.lean       # probe not imported by the root
0
$ python3 -I cmt.py      # every hunk of the 4 Lean files: old and new lines inside /- -/ or -- (nesting tracked)
RBM3D/BA/LWPinsBA.lean: old[20+1] new[20+1] old-in-comment=True new-in-comment=True
RBM3D/BA/LWPinsBA.lean: old[44+1] new[44+1] old-in-comment=True new-in-comment=True
RBM3D/BA/LWPinsBA.lean: old[46+1] new[46+1] old-in-comment=True new-in-comment=True
RBM3D/BA/LWPinsBA.lean: old[48+1] new[48+1] old-in-comment=True new-in-comment=True
RBM3D/BA/LWPinsBA.lean: line count old=112 new=112
RBM3D/BA/Step2CloseBA.lean: old[201+1] new[201+1] old-in-comment=True new-in-comment=True
RBM3D/BA/Step2CloseBA.lean: line count old=260 new=260
RBM3D/BA/TwistPins.lean: old[168+1] new[168+1] old-in-comment=True new-in-comment=True
RBM3D/BA/TwistPins.lean: old[184+1] new[184+1] old-in-comment=True new-in-comment=True
RBM3D/BA/TwistPins.lean: line count old=963 new=963
RBM3D/Graph/BAGGExp.lean: old[78+1] new[78+1] old-in-comment=True new-in-comment=True
RBM3D/Graph/BAGGExp.lean: line count old=534 new=534
hunks outside comments: 0
```
Lines touched = exactly the ticket's list (`TwistPins` doc comments of `BAMainIndTL` :168 and `BAChainTL` :184; `LWPinsBA:20, 44, 46, 48`; `Step2CloseBA:201`; `BAGGExp:78`). Texts match D1 (c) / LC-1. Cited targets in the new comments exist: `Graph/BATermHolds.lean:706 theorem baLWterm_holds`, `Graph/BATermHoldsB.lean:865 theorem baLWtermExp_holds`, `Graph/BAGGExp.lean:358 theorem baGGGamma_holds`, `Graph/BAExp14a2.lean:92 def BALWtermEXPTw`. No frozen signature touched.

## 2. Build, probe compile, axioms, hygiene (audit worktree)
```
$ lake env lean RBM3D/Probe/T2503Pins.lean          # exit=0, output: none (envlean.out: only the `time` line)
$ lake build RBM3D.Probe.T2503Pins                  # 05:18:41-05:25:18 UTC
Build completed successfully (4230 jobs).   probe exit=0; 84 modules built (incl. BA.LWPinsBA, BA.TwistPins, BA.Step2CloseBA, Graph.BAGGExp); warning/error lines on T2503Pins: 0
$ lake build                                        # full library incl. #assert_rbm_axioms, 05:25:18-05:27:10 UTC
Build completed successfully (4382 jobs).   full exit=0; 12 further modules built; `^error` lines: 0; `Built RBM3D.Graph.LWExpCert*`: 0
$ lake env lean ax.lean     # #print axioms of every public probe theorem
'RBM.BA.T2503_tl2Congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2503_k2Member' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2503_famStep1Call' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2503_memberFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2503_famOfS1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2503_memberBase' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2503_tailPassage' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2503_precL_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2503_conclShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2503_baChainFamTL' depends on axioms: [propext, Classical.choice, Quot.sound]
$ wc -l < RBM3D/Probe/T2503Pins.lean; grep -cwE 'sorry|admit|axiom|native_decide|inductive|structure' RBM3D/Probe/T2503Pins.lean
391
0
```
Private theorems (`T2503_shift_mono`, `T2503_posConclFam`, `T2503_flow`, `T2503_win`, `T2503_mem`) are covered by the axioms of the public ones that use them. Every probe `theorem` is proved from merged names (`open private ... from RBM3D.BA.TwistChain` reuses the merged private `TwistChain_*_mix`; no copy).

## 3. Statement: the check's pins equal the probe's (Iff.rfl, uncommitted scratch)
`iffrfl.lean` = imports of the check (`:16-28`) + `import RBM3D.Probe.T2503Pins` + the check's Part 2 verbatim (`:156-293`, root namespace) + 9 examples `<check> ↔ RBM.BA.<probe> := Iff.rfl` (FamTL, S1TL, FamOfS1, FamStep1Call, K2Member, MemberFlow, TL2Congr, BAChainFamTL, RegShape) + one `unfold …; with_reducible rfl` for FamTL.
```
$ lake env lean iffrfl.lean      # exit=0, output lines 0
$ lake env lean neg.lean         # negative control: same file + `T2503_BAMainIndFamTL d R ↔ RBM.BA.BAMainIndTL d R := Iff.rfl`
neg.lean:166:133: error: Type mismatch          neg exit=1
```
The binding D1 (a) pin is the check's text up to the name; no change table needed (report: none). Against merged statements (`tokdiff.py`, tokens of the def bodies):
```
== BAMainIndTL (TwistPins:169) -> T2503_BAMainIndFamTL (probe:33)
  insert TL:  | Fam: ( ∀ n , 0 < sz . lam n ) → ∀ c₁ : ℝ , 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
  insert TL:  | Fam: ( ∀ z' : ℕ → ℂ , BAFamZ sz z c₁ s z' →
  replace TL: z | Fam: z'
  delete TL: ( | Fam:
  insert TL:  | Fam: ∀ z' : ℕ → ℂ , BAFamZ sz z c₁ t z' → let C : = baFMz sz z' ; let μ : = Sizes . seqP ( sz . withLam 0 )
  hunks: 5
== BAMainIndTL -> T2503_BAMainIndS1TL (probe:48)
  insert TL:  | S1: STStep1LoopgL C μ s t → STStep1WeakgL C μ s t →
  hunks: 1
```
So FamTL = `BAMainIndTL` + `BAStep1`'s premises (`0 < lam`, `c₁ ∈ (0,1/2]`, `BAWinBulk`) + family quantifiers on hypotheses (`Fam(s)`) and conclusions (`Fam(t)`); `3 ≤ d`, `∃ 𝔠d ∈ (0,1/100]` before `𝔠, sz, z`, carrier `baFMz sz z'`, law `seqP (sz.withLam 0)`, all six hypotheses / seven conclusions kept. Order checked by eye against T2205 `BAMainInd` (`t/T2205:…/T2205Pins.lean:1715-1733`): identical plus `R sz s t` and TL2. S1 is exactly the ticket's D1 (b). `T2503v1_*` copies (`v1.py`, after `T2502_`→`T2503v1_` and namespace strip): `Exp2UgL` 182↔264, `Step2CoregL` 189↔269, `IngR6gL` 194↔271, `Step6RgL` 210↔284: all `True`.

## 4. Per deliverable: statement, hidden hypotheses, compiled instance
Instance data everywhere: `d = 3`, `sz0`, `zSeq`, `flow_sz0` weakened to `κ = 1/4` (`T2503_flow`, :315), `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3` (`sz0_win_third` weakened, :317), `s ≡ 1/10 < t ≡ 1/2 ≤ T0` (`half_lt_t0`), `STConStInd` by `s1Setup_conStInd_const`; non-main member `T2503_m = BAzSrc sz0 zSeq (2/3) (17/25)` (:319) via `inst_BAFamZ_closed` + `BAFamZ_mono_max`.

| target | statement vs ticket | instance (probe line) | hypotheses left in the instance | verdict |
|---|---|---|---|---|
| D1 (a) `T2503_BAMainIndFamTL` | = check (Iff.rfl); = ticket text | used as hypothesis `hm` of :385/:387 (it is V2a/V2b's target) | — | PASS |
| D1 (b) `T2503_BAMainIndS1TL`, `T2503_FamOfS1` | = check; S1 = TL + Step-1 pair | :357 | `hS1` (V2a 1b target), `hfam` (induction hyp., stochastic) | PASS |
| D2 (a) `T2503_k2Member` | = check; proof: `BAFamZ_mono`→`Fam(0)`, `BAFlowMember_holds`, `baKbound_holds` at `(κ',ε')`, `STKboundgL_congr` + `baFMz_eqAt` | :327 | none | PASS |
| D2 (b) `T2503_famStep1Call` | = check; body is `baStep1_holds' d (by omega) … (fun z' hz' => ⟨K2, (H z' hz').1, (H z' hz').2.2.2.1⟩) hcon` (:112-114), no restatement | :331 (`c₁ = 1/3`), :339 (`c₁` of `BAWinBulk_of_dom_holds 3 _ (1/2) (1/64)`, as `Step1Fam:975-977`) | `hfam` | PASS |
| D2 (c) `T2503_famOfS1` | 16 lines (:124-139) ≤ 180; `𝔠d` from S1 at `(κ',ε',𝔡)`; per member `z''`, congruences there and back | :357, regime `STReg5III` discharged (`nlinarith`, `lam² ≤ 1-t`) | `hS1`, `hfam` | PASS |
| D3 (a) `T2503_memberFlow` | = check; `∃ κ' ε'` before `𝔠 sz z`; flow at `(κ',ε',𝔠,𝔡)`, horizon `≥ t` ∀n, `EvEq` | :348 | none | PASS |
| D3 (b) `T2503_tl2Congr` | = check | :354 (`zSeq` vs `zMod`, `zMod_ev`) | none | PASS |
| D3 (c) `T2503_memberBase` | `STBaseG`, `STG0M` (V3 pins) at `(κ',ε')` + merged `baTwistLoopBase_holds` → `STConclgL ∧ TL2` at `0` per member of `Fam(0)` | :365 (member `T2503_m ∈ Fam(0)`) | `STBaseG 3 …`, `STG0M` (V3, Q5 (b)) | PASS |
| D3 (d) class `t_n = 0` | "mix at the main flow only" (`TwistChain_*_mix`, :259-261) | :387 (`t ≡ 0`) | as D4 (a) | PASS |
| D4 (b) `T2503_tailPassage`, `T2503_conclShift` | route (α): `comp_admissible`, `BAWinBulk_of_dom_holds` at `κ/2`; shift back via `stochDomAt_iff_comp_cover` | :371 (none left), :376 (antecedent `h` = the seven at the tail) | `h` | PASS |
| D4 (a) `T2503_BAChainFamTL` / `T2503_baChainFamTL` | = check; `BAMLOutTL d` from FamTL `STAny`, `STHorizonG`, `STBaseG`, `BATwistLoopBase`, `STG0M` | :385 (`t ≡ 1/2`), :387 (`t ≡ 0`); `BATwistLoopBase 3` discharged by merged `baTwistLoopBase_holds 3` | `hm` (FamTL), `hh` (`STHorizonG`, owed to V3: grep finds no BA producer), `hb`, `hG` (V3) | PASS |
| `T2503_RegShape` (shape) | = check; Step 5 exact type: `baStep5I/II/IV_holds` (:305-307), `baStep5III_holds` at `d = 3` (:308) | elaborated (:303) | — | PASS |

No hypothesis sits in a structure field (no `structure`/`class` in the probe). No cycle: every probe theorem uses only merged names or earlier probe theorems; the pins `FamTL`, `STHorizonG`, `STBaseG`, `STG0M` enter only as explicit hypotheses. No instance is degenerate: `N_0 = 2^21`, `Fam(1/10) = Fam(1/2)` contains the non-main member `T2503_m` (cone `[2/3, T0]`, `T0 ≥ 17/25`), windows and times non-collapsed (`1/10 < 1/2 < 17/25 ≤ T0`). The deterministic hypotheses (`3 ≤ d`, `BAFlow`, `0 < lam`, `c₁` bounds, `BAWinBulk`, the four time bounds, `R`, `STConStInd`, membership) are all discharged at the data.

## 5. D3 / D4 prices re-derived (independent spans of the probe, `price.py`)
```
$ python3 -I price.py
T2503_BAMainIndFamTL: :33-47 15 | T2503_BAMainIndS1TL: :48-58 11 | T2503_FamOfS1: :59-60 2
T2503_tl2Congr: :95-102 8 | T2503_k2Member: :103-109 7 | T2503_famStep1Call: :110-114 5 | T2503_memberFlow: :115-123 9 | T2503_famOfS1: :124-139 16
T2503_memberBase: :142-154 13 | T2503_tailPassage: :155-166 12 | T2503_shift_mono: :167-167 1 | T2503_precL_shift: :169-176 8
T2503_conclShift: :177-195 19 | T2503_posConclFam: :203-232 30 | T2503_baChainFamTL: :235-261 27
pins 28 proofs 45 chain twin 110
V2a (273, 440, 950) V3 (240, 395, 766)
V rows lo/hi 11 14
V2b T2205 spans: 644 minus BAExactLaw 97, minus 100 +12 -> 459
```
(Output lines joined with ` | ` to save space.) With the report's basis (compiled ×1 / ×1.5 / ×2.6 plus its named uncompiled estimates), V2a 273 / 440 / 950 and V3 240 / 395 / 766 reproduce exactly; D3's pieces (`memberFlow` 9, `tl2Congr` 8, `memberBase` 13) are inside those sums. V rows 11 / 12 / 14 reproduce; forecast ≈ 12 < 15, so no first-line flag and no REQ. V2b: see O1.

## 6. Paper deltas
The merged change is comment-only; the probe and its pins are never merged, so this ticket puts no new Lean statement on `main`. The pins' differences from the paper are the family form (D536, `docs/paper-deltas.md:1495`) and `∀ n, 0 < sz.lam n` with the tail passage (D538, `:1497`), both present. The `(κ', ε')` member reading comes from the merged `BAFlowMember` (`Step1Boot:133`), not from this ticket. No `T2503a` candidate is needed. Coverage: PASS (see O2).

## 7. Observations (no statement, instance, build, axiom or delta-coverage effect)
- **O1 (V2b price).** `d4_price.py` hard-codes `V2b=(540,700,1100)`. The basis given in the V2b row (T2205 `:2462-2489, 2521-2615, 2789-3309` = 644 lines, minus about 97, with about 100 lines replaced by 12) gives 459 / 689 / 1,193 at ×1 / ×1.5 / ×2.6. The low end is below the report's 540. V2b is still 1 row and the V forecast does not move.
- **O2 (D536 wording).** The design report says D536 covers the "finite modification `(κ', ε')`". D536's text (`:1495`) covers the family form and `Im m(E, g_s) ≥ κ`, but it does not name `(κ', ε')`. The dispatcher may want to widen D536's wording when V2a's 1b merges `BAMainIndFamTL`.
- **O3 (role).** The design report recommends `prover-hard` for V2a's 1b, but the ticket (T2379 `:167`) says `prover-max`. This is the dispatcher's choice and not a statement issue.
- **O4 (D1 (c) LC-1 tail).** Finding F1 says `LWPinsBA.lean:50, 52` (`BASTLWB`, `BASTLWT` "owed") are stale in the same way. They are outside this ticket's lines; leave them for the next LC-1 touch.
- **O5 (scratch).** The audit's first scratch files (`iffrfl.lean`, `tokdiff.py`, `cmt.py`, `price.py`, `envlean.out`, `build_*.log`) went into the shared `T2503/` scratch directory, which the stage-1 prover had also used. Prover scratch files with the same names (at least `iffrfl.lean`, `tokdiff.py`) were overwritten. The audit copies are in `T2503/audit1/`. No deliverable depends on scratch.

## 8. Verdict
| deliverable | verdict |
|---|---|
| D1 (a) binding `BAMainIndFamTL` (pinned unchanged, = check by Iff.rfl) | PASS |
| D1 (b) S1 + wrapper (needs nothing beyond D2/D3 + 9 merged congruences + TL2 congruence) | PASS |
| D1 (c) doc comments + LC-1 (comment-only, full `lake build` passes) | PASS |
| D2 (a)/(b)/(c) K2, family Step-1 call at exact type, wrapper | PASS |
| D3 (a)-(d) members at `(κ', ε')`, TL2 congruence, per-member base, class `t_n = 0` | PASS |
| D4 (a)-(c) family chain twin compiled, tail passage (α) compiled, price, V forecast 12 | PASS |
| Acceptance: probe (exit 0, 3 axioms, 0 forbidden, 391 ≤ 400, `d = 3` instances), check (Iff.rfl), diff scope, report (179 ≤ 250, first line) | PASS |

**Overall: PASS.** No stop rule fires. No dispatcher sign-off is needed (answer (3) already decides the `(κ', ε')` reading). Merge per ticket: `docs/reports/T2503-design.md` and the four comment-only Lean files; the probe stays on `t/T2503`.
Written Wed Oct 14 05:28:27 UTC 2026 (`date -u`).
