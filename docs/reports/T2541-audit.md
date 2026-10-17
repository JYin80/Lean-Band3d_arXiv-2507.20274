Auditor model: claude-opus-5-5

# T2541 audit, round 2 (Sat Oct 17 19:09:03 UTC 2026)

Inputs: ticket, Amend 1, Amend 2, `docs/tickets/T2541-files.txt` (69 files), prove report (incl. repair section).
Branch `t/T2541` = 2a589ecd (base 2a77235e). Audit worktree `RBM3D-wt/T2541-audit2` (detached at 2a589ecd).
Scripts are this auditor's own, written fresh for round 2 (scratchpad `T2541/a2/`: `lex.py`, `cmp.py`, `hdr.py`,
`incom.py`, `names.py`, `names2.py`, `attr.py`, `attr2.py`, `labels.py`, `plab.py`, `acc.sh`).
Target: comments only; no statement is added or changed, so audit items 1-3 reduce to "no code token changed".

## 1. Diff scope and code identity
```
$ git diff --name-only main...t/T2541 | sort | diff - <(sort docs/tickets/T2541-files.txt) && echo "changed == list"
changed == list
$ git diff --shortstat main...t/T2541
 69 files changed, 2014 insertions(+), 2873 deletions(-)
$ git diff --name-only 2a77235e main | grep -F -f docs/tickets/T2541-files.txt; echo "overlap rc=$?"   # overlap rc=1
$ python3 -I cmp.py <repo> 2a77235e t/T2541 docs/tickets/T2541-files.txt      # identical: 69 files / different: 0
$ python3 -I hdr.py <repo> 2a77235e t/T2541 docs/tickets/T2541-files.txt     # copyright header identical 69 / 69
```
`lex.py`: nested `/- -/`, doc comments, `--` to EOL, strings with escapes, char literals (`'` after an identifier char is
a prime); trailing blanks and blank lines dropped before comparing. `set_option ... in` followers: base and branch both
have a `/-!` after `set_option maxHeartbeats 1600000 in` at the end of `GUEEntry2.lean` (branch :907-908); others are
`--` / `/--` before declarations. The repair commit 2a589ecd changes 2 files (`GUEEntry2.lean`, `GreenCore.lean`),
docstring text only.

## 2. Build, check file, axioms (audit worktree)
```
$ lake build      # start Sat Oct 17 18:52:26 UTC 2026
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
exit 0            # end Sat Oct 17 19:08:33 UTC 2026
errors: 0  sorry: 0;   $ lake env lean docs/tickets/checks/T2541-check.lean   # check rc=0 error lines: 0
$ lake env lean axioms.lean      # import RBM3D; #print axioms
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gueEntryMixBA'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKbound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baConArg''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
sorry/admit/native_decide tokens: 0  axiom decls: 0        (69 files)
```
Compiled nonempty instance: not applicable (no endpoint theorem added or changed; code identical).

## 3. Ticket acceptance greps (branch)
```
$ bash acc.sh
ticket grep hits:       99
CJK hits: 0
grep -L '/-!': (end)
Amend 1 grep: rc=1
texref --scan branch lines:        0          (base copies of the 69 files: 149)
$ python3 -I incom.py . <list> '<ticket pattern>' i
matches in code: 94   in comments: 10
GUEHyp.lean:218/552/826/927 [h730]   GUEPathBoundsBA.lean:55 [h745][h746], :271 [h745], :376 [h746]
GreenCond2.lean:411 [control] "local law at a deterministic control"   GreenLocal.lean:12 [control] (same)
```
The 10 comment hits are hypothesis names of the documented statements or the English word "control"; code hits are
unchanged identifiers. Rule-1 words in comments (route, wave, stage, owed, borrowed, refuted, superseded, structural,
was replaced, earlier version, no longer, moved from, renamed, successor, the old, now, landing/stop line, Fable, Jun):
only `row` (228, all matrix/kernel rows) and `Jun` in the copyright headers. Planning labels / RBM1D/RBM2D / hashes:
only `2097152` (`ConArg.lean:1667`, `N = 128^3`). `d = 3` mentions: `EKPins.lean:119` (the `d = 3` absorption of (A.19)),
`FlowPins.lean:28, 673` (explicit data in `RBM.BA.FlowPinsInst`); no scope claim.

## 4. Repair of round-1 findings
- F1: `GUEEntry2.lean:794-798` now describes `gueEntryMixBA'` from its body. Checked against :800-889: one
  `filter_upwards` with `hδ` (`δ n ≤ N^{-c₀}`), `hbw` (bandwidth), `hwin` (window); `c₁ := min c₀ (𝔠 * d / 2)`;
  `δ' := max (δ n) (Real.sqrt w₀)`; `hsub` (event inclusion); `GUEEntry_union hd sz n hg hgΛ hκ hr ...` (`hr := hrdata n`,
  `BAReal`); `mixEntry_final_arith`. Accurate. Resolved.
- F2: `GreenCore.lean:1634` now reads `GreenCore_decayRHS d L W c D Φ_t Ψ_t ([x], [y])`, matching the body of
  `GreenCore_decayConcl` (:1640). Resolved.

## 5. Amend 2 items 1-5 (rerun independently, all 69 files)
Item 1, whole backticked identifier-shaped spans vs identifiers of the code of `RBM3D/**/*.lean` (`names.py`):
```
backticked spans: {'not identifier-shaped (formula/symbol)': 6478, 'file name': 316, 'final-TeX label': 196,
                   'exists in code': 4867, 'subscript notation': 119}
unexplained identifiers: 38
```
37 of the 38 are single mathematical symbols (`λ`, `Ĵ`, `𝓛`, `𝒞₁`, `𝒞₂`, `𝒮₁`, `𝒮₂`, `𝒜'` x13, `𝔛'`, `𝔗` x5, `Ũ`, `tΘ` x9,
`ΘMΘ` x2). The 38th is a dotted Lean name that does not exist:
```
$ sed -n 561,562p RBM3D/BA/GreenMinor3.lean
/-- The polynomial `Y^X_{uy}` in the centred entries (as a family): the linear terms and the quadratic terms, bounded by
`DiffBd.add`, `.smul`, `.mul` (orders `1` and `1 + 1`, lowered by `Ψ ≤ 1`).  ...
$ grep -nE "^(theorem|lemma|protected theorem) DiffBd\.\w+" RBM3D/Green/MinorDiff.lean | sed 's/ {.*//'
DiffBd.le_self mono_I mono_n mono_M mono_c mono_p congr delta shift neg mul   (lines 228-318; condensed to one line)
$ sed -n 575,600p RBM3D/BA/GreenMinor3.lean | grep -oE "(GreenMinor_)?DiffBd[._][A-Za-z]+" | sort | uniq -c
   2 DiffBd.mul
   5 GreenMinor_DiffBd_add
   6 GreenMinor_DiffBd_smul
```
`DiffBd.add` and `DiffBd.smul` (the `.smul` shorthand, `names2.py`: `DOT GreenMinor3.lean 562 .smul prefix DiffBd`) do not
exist; the proof of `GreenMinor_DiffBd_modelX` uses `GreenMinor_DiffBd_add` / `GreenMinor_DiffBd_smul` (defined in the
same file, :141, :152) and `DiffBd.mul`. The file's own section docstring (:112) says the band calculus has no sum rule.
Pre-existing on the base (base :567). Finding F3.
Names inside formulas (`names2.py`, len >= 5, `_` or camelCase): all are final-TeX labels with their prefix, subscripted
symbols (`X_block`, `BAK_ab`, `STeeMg_u`, `Mart_k`, `F_out`, `a_out`, ...) or `maxDist` (round-1 O1, unchanged).
Item 2, module/file paths (`names.py`): 361 path tokens; not a file or directory: 6, none a defect: `Y/N`, `X/N`, `X/N³`,
`C₂/L` (quotients), `Propagator/{Basic,Deriv}.lean` x2 (`KBase.lean:20, 78`; both `RBM3D/Propagator/Basic.lean` and
`Deriv.lean` exist). 316 backticked `*.lean` names all exist.
Item 3, file attributions (`attr.py`: `` `Name` (/in/of/from) `Path` ``, 208 pairs; `attr2.py`: `` `Path` (`a`, `b`) ``, 86
pairs). Flags read one by one; all are lists in the sentence (names spread over the listed files) or a proof that uses the
name, except one:
```
$ sed -n 13,14p RBM3D/BA/GUEDuhamelBA.lean
The drift remainder of one grid step of the GUE phase at the block Anderson carrier, `Duhamel_drift_remainder_aeBA`, used by
`gueGrid_loop_duhamel` in `BA/GUEDuhamelBA2`.  The band counterparts are in `Universality/GUEPhase`:
$ grep -rn "theorem gueGrid_loop_duhamel\b" RBM3D
RBM3D/Universality/GUEPhase/DuhamelC.lean:1485:theorem gueGrid_loop_duhamel {d : ℕ} (sz : Sizes d) {κ τU : ℝ} ...
$ grep -n "gueGrid_loop_duhamel\|Duhamel_drift_remainder_aeBA" RBM3D/BA/GUEDuhamelBA2.lean | head -3
13:main theorem **`gueGrid_loop_duhamelBA`**, the block Anderson version of `gueGrid_loop_duhamel`
19:bound from `Duhamel_drift_remainder_aeBA`.
```
The module docstring attributes `gueGrid_loop_duhamel` to `BA/GUEDuhamelBA2`, which does not contain it; the consumer there
is `gueGrid_loop_duhamelBA`. Pre-existing on the base (base :10). Finding F4.
Item 4 (`labels.py`, `plab.py`): 206 backticked colon labels, all in `paper-labels.tsv`; 284 number-label pairs, 0 mismatch;
119 backticked `(label)` tokens: 21 not final-TeX labels, of which 15 are formulas (`(+,-)`, `(n+1)`, `(∞→∞)`, ...) and 6
are in `EMCTE2BA.lean`/`EMn2BA.lean`: see O2. Item 5: `[Rr]oute` in comments 0; "Proof outline" 2.

## 6. Paper deltas
No Lean statement changed; no Lean/paper difference; none proposed (none expected).

## Findings
- **F3 (RETURN, Amend 2 item 1).** `RBM3D/BA/GreenMinor3.lean:561-562`: `` `DiffBd.add`, `.smul`, `.mul` `` names two
  declarations that do not exist (`DiffBd.add`, `DiffBd.smul`); the proof below uses `GreenMinor_DiffBd_add`,
  `GreenMinor_DiffBd_smul` and `DiffBd.mul`.
- **F4 (RETURN, Amend 2 item 3).** `RBM3D/BA/GUEDuhamelBA.lean:13-14`: "`Duhamel_drift_remainder_aeBA`, used by
  `gueGrid_loop_duhamel` in `BA/GUEDuhamelBA2`" attributes `gueGrid_loop_duhamel` (in
  `Universality/GUEPhase/DuhamelC.lean`) to `BA/GUEDuhamelBA2`; the declaration there is `gueGrid_loop_duhamelBA`.
Both are on the base and were not found in round 1; both are one-line comment edits.

## Observations (no RETURN)
- O1. `KDecayBA.lean` `maxDist` inside formulas (round-1 O1) is unchanged; the Lean name is `KLmaxDist`.
- O2. `EMCTE2BA.lean:12-30` uses `(EMCTE2)`, `(jaklsdufowe)`, `(uywy7723r3rf)` and `EMn2BA.lean:30` `(HK)` as names of
  estimates. They are not labels of the final TeX (`grep -rn jaklsdufowe paper/final/tex paper/tex`: no output); line 20
  identifies the second and third as (2.22), (2.23) of [DYYY25]. Rule 2 cites other papers bibliographically; the
  dispatcher may want `[DYYY25, (2.22)]` / `[DYYY25, (2.23)]` instead of their TeX labels.

## Verdict
**RETURN** (comments-only target; code identity, diff scope, build, check file, axioms, ticket greps, Amend 1, round-1
F1/F2 repairs, Amend 2 items 2, 4, 5 pass). Caused only by Amend 2 (items 1 and 3). This is the second RETURN on T2541,
so rule (B) stops the automatic repair here; no further dispatcher decision about the statements is needed.

Required for resubmission:
1. `RBM3D/BA/GreenMinor3.lean:561-562`: replace `` `DiffBd.add`, `.smul`, `.mul` `` by names that exist, e.g.
   `` `GreenMinor_DiffBd_add`, `GreenMinor_DiffBd_smul`, `DiffBd.mul` ``.
2. `RBM3D/BA/GUEDuhamelBA.lean:13-14`: say that `Duhamel_drift_remainder_aeBA` is used by `gueGrid_loop_duhamelBA` in
   `BA/GUEDuhamelBA2` (the block Anderson version of `gueGrid_loop_duhamel`), or drop the file attribution.
3. Comments only; rerun the strip comparison (69 identical), the ticket grep, Amend 2 items 1-3 on **all 69 files**
   (not only the changed lines), and `lake build RBM3D.BA.GreenMinor3 RBM3D.BA.GUEDuhamelBA`.
