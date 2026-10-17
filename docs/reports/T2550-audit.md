Auditor model: claude-opus-5-5

# T2550 audit (round 1), written Sat Oct 17 09:48:01 UTC 2026

Ticket T2550 + Amend 1. Report-only (no Lean change, no endpoint theorem). Worktree `RBM3D-wt/T2550-audit1` at `t/T2550` = `81a23bf7`.

**Verdict: PASS.** No dispatcher sign-off needed.

## 1. Scope of the diff

```
$ git diff --name-only main...t/T2550 ; git diff main...t/T2550 --name-only -- '*.lean' | wc -l
docs/PAPER-VS-LEAN.md
       0
$ git diff 1a8c2c11 main --name-only | grep -v '^docs/'      (no output: main moved only in docs/)
$ wc -l docs/PAPER-VS-LEAN.md
     704            (limit 720)
```

## 2. Build, axioms, check file (audit worktree)

```
$ lake build RBM3D.Main.FinalShape 2>&1 | grep -E "error|Build completed"
Build completed successfully (4420 jobs).
$ lake build 2>&1 | grep -E "error|axiom audit|Build completed"
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
$ lake env lean docs/tickets/checks/T2550-check.lean ; echo exit $?    ->  exit 0, 0 error lines
```
Axiom block of the document recomputed (`#print axioms` of each of its 10 names, diff against the document):
```
$ lake env lean ax.lean ; diff <(head -10 ax.out) docax.txt
exit 0
doc axiom block identical (10 lines)
'RBM.BA.baStep5III_holds_any' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Deliverable 1: every Lean name exists; quoted statements verbatim

Independent extractor (`names.py`: backticked spans outside fences, identifier-like tokens; 265 tokens, 255 `#check @`
lines after dropping `.lean`/`.pdf` paths; opens `RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA RBM.Endpoints RBM.Univ RBM.Path RBM.Loop RBM.Gauss.SizesInst`):
```
$ lake env lean chk.lean ; echo exit $? ; grep -c error chk.out
exit 1
42
```
The 42 unknown tokens, classified by hand (none is a Lean declaration the document claims to exist):
math notation (`G_xx … H_ij … S_xy Tr_block gvar_c lim_ max_ sup_ p_GUE A.Nonempty`), namespaces/directories (`RBM.BA RBM.Endpoints RBM.Univ Chain
Evolution Gauss Graph Green Induction Kernel Loop Main Propagator Test Universality`), paper labels `lem_ConArg lem_GbEXP` (in the tsv),
the command `assert_rbm_axioms`, `atTop` (Filter), dot notation `sz.Admissible sz.seqXmat sz.withLam`, and the private `FinalShape_bulk4` (called "the private lemma").
```
$ lake env lean chk2.lean   (#check @RBM.Gauss.Sizes.Admissible/.seqXmat/.withLam, @Filter.atTop)  ->  exit 0
$ grep -n "private theorem FinalShape_bulk4" RBM3D/Main/FinalShape.lean
193:private theorem FinalShape_bulk4 : ∃ g0 E κ : ℝ, 0 < g0 ∧ g0 ≤ 3 / 10 ∧ 0 < κ ∧ BAbulk 4 4 g0 κ E := by
```
The six names the ticket lists compile (in `chk.out`): `RBM.BA.baStep5III_holds_any`, `RBM.BA.baThm27L_all`,
`RBM.Endpoints.Thm27`, `RBM.Endpoints.Thm27_of_L32`, `RBM.BA.baThm27L_three`, `RBM.BA.baThm27L_any`.

Quoted statements: the changed block, line by line, against its source; then every line of all five ```lean blocks:
```
39 RBM3D/Main/FinalShape.lean | def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d
42 RBM3D/Main/FinalShape.lean | theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27
46 RBM3D/Main/FinalShape.lean | theorem final_shape : RBM.Univ.UNL32 →
47 RBM3D/Main/FinalShape.lean |     (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27
271 RBM3D/BA/UNBUniv.lean | theorem baThm27L_all (h32 : UNL32) : ∀ d : ℕ, 3 ≤ d → BAThm27L d
276 RBM3D/BA/UNBUniv.lean | theorem baThm27L_three : UNL32 → BAThm27L 3
$ python3 -I verb.py docs/PAPER-VS-LEAN.md .
blocks 5 lines verbatim 242 not 0
```

## 4. Deliverable 2: Theorem 2.7 at every d ≥ 3; no "pending" wording

```
$ grep -nEi 'T2[0-9]{3}|DECISIONS|paper-delta|ticket|prover|auditor|dispatcher|\bgate\b|pinned|\bowed\b|pending' docs/PAPER-VS-LEAN.md ; echo exit $?
exit 1
$ grep -nEi 'to be merged|registry|not yet merged' ; grep -nEi 'only (at|for|in) .?d = 3|d = 3 only|proved at .?d = 3'   ->  exit 1, exit 1
$ grep -nE 'd = 3' docs/PAPER-VS-LEAN.md | cut -c1-110
110:... at each `d`. The case `d = 3` is `RBM.BA.baThm27L_three`.
139:- `RBM3D/Main/BandTerminal.lean`, §Instances. The size sequence `RBM.Gauss.SizesInst.sz0`: `d = 3`, ...
145:- `RBM3D/BA/MAPins.lean`. The class sequence `RBM.Univ.BAInst.S0`: `d = 3`, ...
148:- `RBM3D/Main/FinalShape.lean`. ... (five at `sz0`, five at `S0`; the `d = 3` conjuncts of `Thm27` are `.2 3 le_rfl`) ...
```
Lines 139, 145, 148 are the `d = 3` instances, line 110 the `d = 3` corollary. Lines 108-110 state `Thm27 := ∀ d, 3 ≤ d →
BAThm27L d`, proved by `baThm27L_all` from `UNL32` and `baStep5III_holds_any`, matching `FinalShape.lean:39,42`
(`Thm27_of_L32 ... := RBM.BA.baThm27L_all`).

## 5. Deliverable 3 + Amend 1: the d = 4 instance (doc lines 149-154) against `FinalShape.lean:130-232`

| Document claim | Source | OK |
|---|---|---|
| `(final_shape h32).2 4` applied | `:222 have h := (final_shape h32).2 4 (by norm_num)` | yes |
| `Sizes 4`, `L n = 4`, `W n = (2(n+1))^5`, `lam n = g₀` | `:136-139 FinalShape_cls4` | yes |
| `Admissible (1/8) (1/10)` proved for every `g₀ ∈ (0, 10]` | `:148 FinalShape_cls4_adm (h0 : 0 < g0) (h10 : g0 ≤ 10)` | yes |
| `0 < g₀ ≤ 3/10`, `κ > 0`, `BAbulk 4 4 g₀ κ E`, via `BAbulk_iff_exists` | `:193-203` | yes |
| real-axis solution of (2.32) at `(4,4)` | `BAzztE_data`: `BASelf d L (√t₀·g) (BAflowE z m : ℂ) …` (real energy); (2.32) = `self_m` p. 11 | yes |
| bulk for every `n`; `BAendDom` nonempty at every `n` | example conclusion `:218-220`, `FinalShape_dom4 :205` | yes |
| all five conjuncts decol, locSC, QUE, BUniv, QDiff | `:223-230` `h.1`, `h.2.1`, `h.2.2.1`, `h.2.2.2.1`, `h.2.2.2.2` | yes |
| BUniv at `k = 1`, `E' = 0`, `bump` | `:227 … hadm 1 le_rfl κ hκ E (…) 0 (by norm_num) UNInst.bump …` vs `BAEnd_BUnivL` (`UNPins.lean:304-308`: `k, κ, E, E', O`) | yes |
| `UNL32` the only hypothesis | `:217 example (h32 : UNL32)` | yes |

BDC-C1: `grep -nEi 'vanish|empty bulk|coupling (→|->|tends) 0|g ?→ ?0'` matches only line 149 ("nonempty bulk"); the
only reason given for the constant coupling is that the bulk witness is built at one fixed coupling (line 153). BDC-C2:
all five conjuncts are named; the only `d = 3` BUniv text (line 143, `bUniv_holds` at `sz0`) is the band model, not the `d = 4` example.
The old data `L n = 4(n+1)`, `lam n = (2(n+1))^{-6}` now appear only in the `sz0` bullet (line 139), where they are correct.

## 6. Deliverable 4: axiom audit description (doc lines 117-122) against `RBM3D/Test/Axioms.lean`

```
28:def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
34:    if (`RBM).isPrefixOf n then acc.push n else acc
35:  if names.size < 100 then
40:    let extra := axs.filter fun a => !allowedAxioms.contains a
$ tail -1 RBM3D.lean   ->  #assert_rbm_axioms
```
The description (constants with prefix `RBM`, only the three axioms, no further allowed axiom, floor `100`, last
command of `RBM3D.lean`) matches; no registry wording remains (grep above).

## 7. Deliverable 5: references (final PDF, PyMuPDF; `pdftotext` not installed; PDF index = printed page, checked by last line of pp. 14, 15)

```
pages: 106
(2.52) on pages [15]
Ito on pages [14, 78]
14 | ... By Itˆo’s formula, we can derive the following SDE satisfied by the G-loops, ...
78 | ... The derivation of the loop hierarchy (2.47) by Itˆo’s formula does not use the special form of the matrices Eai ...
14 | Definition 2.14: True | (2.47): True
$ grep Def_Ktza / eq:initial_K paper-labels.tsv
Def_Ktza	definition	2.14	14
eq:initial_K	equation	2.52	15
```
Both reference edits ("(2.52) is on p. 15"; "Itô's formula (p. 14; ... p. 78)") are correct. Independent adjacency check
of `(x.y) (p. N)` and `Theorem|Lemma|… x.y …, p. N` against the tsv: `checked 6 mismatch 1`; the one flag (line 477,
"Lemma 3.6 in [69] … p. 15") is a citation of another paper on the row of Lemma 2.15 (`lem_WI_K`, p. 15): correct.

## 8. T2535 audit recheck items

1. Final forms: names compile (§3), `.2 3 le_rfl` (`FinalShape.lean:89`), d = 4 bullet rewritten (§5). 2. d = 4 bulk: now the proved nonempty bulk. 3. (2.52) page fixed (§7). Resolved.
4. Optional `Ring.inverse` sentence: omitted, which the ticket allows ("otherwise omit"). See Observation 1.

## 9. Paper deltas

No Lean statement changed; the edits add no Lean/paper difference. Nothing to cover.
## Observations (no RETURN)

1. Prove report (d) 1 says `grep -rn "IsUnit" RBM3D/BA` finds only private lemmas. False as stated:
   `KBase.lean:244 theorem BATheta_isUnit (… (hr : BAReal d L g κ E m) … (ht1 : t < 1) …) : IsUnit (1 - (t : ℂ) • BAMss …)`
   is public. It is stated at a real energy `E` with `BAReal`, not on `BAendDom`, so the ticket's optional item 6
   ("if the Lean source shows it [on `BAendDom`]") may still be omitted. No statement, instance, build or delta is affected.

**Result.** T2550: PASS (single target: the document). Diff only `docs/PAPER-VS-LEAN.md`; no dispatcher sign-off needed.
