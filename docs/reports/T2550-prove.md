Prover model: claude-sonnet-5-5

## (a) Math preflight — 2026-10-17 09:01:14 UTC

(i) No exponents. The ticket is report-only (one Markdown file, no Lean change); no exponent, threshold or constant is involved.

(ii) Not applicable.

Verdict: PASS

## (b) Script output (stage 1b, written 2026-10-17 09:38 UTC)

Branch `t/T2550` at `81a23bf7` (one commit on merge-base `1a8c2c11`); only `docs/PAPER-VS-LEAN.md` changed. No Lean file changed.

```
$ git diff main...t/T2550 --name-only ; git diff HEAD~1 --stat
docs/PAPER-VS-LEAN.md
 docs/PAPER-VS-LEAN.md | 35 ++++++++++++++++++++++-------------
$ wc -l docs/PAPER-VS-LEAN.md
704
```

### Edits (git diff, deliverable by deliverable)

- Item 1: the block of quoted statements now holds the source statements of `Thm27`, `Thm27_of_L32`, `final_shape` (`RBM3D/Main/FinalShape.lean`) and `baThm27L_all`, `baThm27L_three` (`RBM3D/BA/UNBUniv.lean`), written by script `quote.py`. No "pending" or "to be merged" wording existed in the version on `1a8c2c11`; the grep below prints nothing.
- Item 2: no change needed; the "Dimension" paragraph (line 108-110) already states `Thm27 := ∀ d, 3 ≤ d → BAThm27L d`, proved by `baThm27L_all` from `UNL32` and `baStep5III_holds_any`.
- Item 3: the `d = 4` bullet of `FinalShape.lean` rewritten (lines 148-154).
- Item 4: the "Axioms" paragraph rewritten (lines 117-122); the axiom block gains `baThm27L_all`.
- Item 5: two reference edits: (2.52) page and the Itô formula page (see PDF evidence).
- Item 6: omitted (no merged lemma states that `1 − M^{(σ₁,σ₂)}` is invertible on `BAendDom`; see (d)).

```
$ git diff HEAD~1 | grep '^[+-]' | grep -v '^+++\|^---' | cut -c1-170     (the d = 4 and axioms text)
+-- namespace RBM.Endpoints (RBM3D/Main/FinalShape.lean), with `open RBM.Univ`
-theorem RBM.Endpoints.Thm27_of_L32 : RBM.Univ.UNL32 → Thm27
-theorem RBM.BA.baThm27L_all : RBM.Univ.UNL32 → ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d
-theorem final_shape :
-  RBM.Univ.UNL32 →
-    (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧ Thm27
+theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27
+theorem final_shape : RBM.Univ.UNL32 →
+    (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27
+-- namespace RBM.BA (RBM3D/BA/UNBUniv.lean), with `open RBM.Univ`
+theorem baThm27L_all (h32 : UNL32) : ∀ d : ℕ, 3 ≤ d → BAThm27L d
+theorem baThm27L_three : UNL32 → BAThm27L 3
-**Axioms.** The command `#assert_rbm_axioms` (file `RBM3D/Test/Axioms.lean`, run as the last command of `RBM3D.lean`) fails
-the build unless every declaration in the namespace `RBM` depends only on `propext`, `Classical.choice`, `Quot.sound`. The
-command `#print axioms` on the theorems of the table, on `band_terminal`, `final_shape` and `baThm27L_three` prints
+**Axioms.** The command `#assert_rbm_axioms` (file `RBM3D/Test/Axioms.lean`, run as the last command of `RBM3D.lean`) walks
+every constant of the environment whose name starts with `RBM`, computes the axioms it depends on (as `#print axioms` does) and
+fails the build unless each of them is `propext`, `Classical.choice` or `Quot.sound`. There is no further allowed axiom. The command also fails
+if it finds fewer than `100` such constants, so that a mistyped namespace cannot make the audit pass vacuously. In particular no `sorry` and no declared `axiom`
+occurs in `RBM`; every statement that is not proved is a hypothesis, a theorem parameter or a structure field. The command `#print axioms` on the theorems of the table, 
+`baThm27L_all` and `baThm27L_three` prints
+'RBM.BA.baThm27L_all' depends on axioms: [propext, Classical.choice, Quot.sound]
-  with `UNL32` the only hypothesis. A further example at `d = 4` applies the conjuncts decol, locSC, QUE and QDiff of `Thm27` on `Sizes 4` at `L n = 4(n+1)`, `W n = (2(n
-  `lam n = (2(n+1))^{-6}`, admissible at `(1/8, 1/10)`, with `UNL32` the only hypothesis.
+  with `UNL32` the only hypothesis. A further example applies the `d = 4` part of `Thm27`, that is `(final_shape h32).2 4`, to concrete data over a nonempty bulk. The da
+  `Sizes 4` with `L n = 4`, `W n = (2(n+1))^5` and the constant coupling `lam n = g₀`, admissible at `(𝔠, 𝔡) = (1/8, 1/10)` (the proof of `Admissible (1/8) (1/10)` is in
+  `g₀ ∈ (0, 10]`), and a triple `(g₀, E, κ)` with `0 < g₀ ≤ 3/10`, `κ > 0` and `BAbulk 4 4 g₀ κ E`, obtained from a real-axis solution of (2.32) at `(d, L) = (4, 4)` (th
+  `FinalShape_bulk4`, using `RBM.BA.BAbulk_iff_exists`). The bulk is nonempty: `κ ≤ ρ_N(E)` holds for every `n`, and the end domain `BAendDom` (§2.12) is nonempty at eve
+  constant `g₀` because the witness of the bulk is built at one fixed coupling, so a constant sequence is an eventual witness directly. All five conjuncts of `Thm27 4` (
+  data, the universality conjunct at `k = 1`, `E' = 0` and `RBM.Univ.UNInst.bump`, with `UNL32` the only hypothesis.
-- **Paper.** The loop hierarchy (2.47) (p. 14) is derived by Itô's formula (stated on p. 78). Gaussian integration by parts is used for the light-weight terms (pp. 24, 5
+- **Paper.** The loop hierarchy (2.47) (p. 14) is derived by Itô's formula (p. 14; the same derivation is applied to twisted loops on p. 78). Gaussian integration by par
-- **Paper.** `𝒦` is "the unique solution" of the convolution tree equations (2.50) with the initial data (2.52) (Definition 2.14, p. 14), and has an explicit tree repres
+- **Paper.** `𝒦` is "the unique solution" of the convolution tree equations (2.50) with the initial data (2.52) (Definition 2.14, p. 14; (2.52) is on p. 15), and has an 
```

### Acceptance 1: `#check @<name>` for every Lean name of the document

The name list is extracted by script (`names.py`: every backticked span outside code fences, identifier-like tokens; `gen.py` writes the file; the bare names are checked under `open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA RBM.Endpoints RBM.Univ RBM.Path RBM.Loop`; `sz0_admissible`, `UNModel.ba` and the `Sizes` fields with full names). Scratch file `T2550/chk_all.lean` is not committed.

```
$ grep -c '^#check' chk_all.lean
226
$ lake env lean chk_all.lean > chk_all.out 2>&1 ; echo "exit $?" ; grep -c error chk_all.out
exit 0
0
$ grep -n "baThm27L_all\|baStep5III_holds_any\|baThm27L_three\|Thm27_of_L32\|^RBM.Endpoints.Thm27 " chk_all.out | cut -c1-120
31:RBM.BA.baStep5III_holds_any : ∀ (d : ℕ),
35:RBM.BA.baThm27L_all : RBM.Univ.UNL32 → ∀ (d : ℕ), 3 ≤ d → RBM.BA.BAThm27L d
41:RBM.BA.baThm27L_three : RBM.Univ.UNL32 → RBM.BA.BAThm27L 3
52:RBM.Endpoints.Thm27 : Prop
53:RBM.Endpoints.Thm27_of_L32 : RBM.Univ.UNL32 → RBM.Endpoints.Thm27
$ ls RBM3D/Main/FinalShape.lean RBM3D/BA/UNBUniv.lean ...  (every `RBM3D/...lean` path of the document)
$ grep -oE 'RBM3D/[A-Za-z0-9_/]+\.lean' docs/PAPER-VS-LEAN.md | sort -u | while read f; do [ -f $f ] || echo MISSING $f; done
(no output)
$ lake env lean docs/tickets/checks/T2550-check.lean ; echo "exit $?"      (on t/T2550)
exit 0
```

### Acceptance 2: quoted Lean statements copied by script from the source

```
$ python3 quote.py block.txt        (reads RBM3D/Main/FinalShape.lean, RBM3D/BA/UNBUniv.lean; regex from the keyword to `:=`)
-- namespace RBM.Endpoints (RBM3D/Main/FinalShape.lean), with `open RBM.Univ`
def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d
theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27
theorem final_shape : RBM.Univ.UNL32 →
    (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27
-- namespace RBM.BA (RBM3D/BA/UNBUniv.lean), with `open RBM.Univ`
theorem baThm27L_all (h32 : UNL32) : ∀ d : ℕ, 3 ≤ d → BAThm27L d
theorem baThm27L_three : UNL32 → BAThm27L 3
$ python3 quotes.py     (every declaration of the 5 ```lean blocks, docstrings of the source removed, must be a contiguous substring of some RBM3D/**/*.lean)
verbatim 67 not 0 blocks 5
```

The `d = 4` example (`FinalShape.lean:217-232`) builds (`lake build RBM3D.Main.FinalShape` on the branch):

```
$ lake build RBM3D.Main.FinalShape 2>&1 | tail -1
Build completed successfully (4420 jobs).
$ lake env lean RBM3D.lean          (the last command of RBM3D.lean is #assert_rbm_axioms)
axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
$ #print axioms of every name in the document's axiom block (lines 125-134); diff against the document
doc axiom block identical to #print axioms output
$ #print axioms RBM.BA.baStep5III_holds_any
'RBM.BA.baStep5III_holds_any' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The `d = 4` bullet of the document against the file (source lines):

```
$ sed -n '135,139p;217,219p;228,229p' RBM3D/Main/FinalShape.lean | cut -c1-170
/-- The class sequence at `d = 4`: `L = 4`, `W_n = (2(n+1))^5`, `lam = g₀`. -/
private def FinalShape_cls4 (g0 : ℝ) : Sizes 4 where
  L := fun _ => 4
  W := fun n => (2 * (n + 1)) ^ 5
  lam := fun _ => g0
example (h32 : UNL32) : ∃ g0 E κ : ℝ, 0 < κ ∧ (FinalShape_cls4 g0).Admissible (1 / 8) (1 / 10) ∧
    (∀ᶠ n in atTop, BAbulk 4 ((FinalShape_cls4 g0).L n) ((FinalShape_cls4 g0).lam n) κ E) ∧
    ∀ n, ∃ z : ℂ, BAendDom (FinalShape_cls4 g0) κ (1 / 10) n z := by
  have _ := h.2.2.2.1 (by norm_num) (1 / 8) (1 / 10) (FinalShape_cls4 g0) hadm 1 le_rfl κ hκ E (Eventually.of_forall fun _ => hb) 0
    (by norm_num) UNInst.bump UNInst.bump_testFun
$ grep -n "FinalShape_cls4_adm\|theorem FinalShape_bulk4\|theorem FinalShape_dom4" RBM3D/Main/FinalShape.lean | cut -c1-150
148:private theorem FinalShape_cls4_adm {g0 : ℝ} (h0 : 0 < g0) (h10 : g0 ≤ 10) :
193:private theorem FinalShape_bulk4 : ∃ g0 E κ : ℝ, 0 < g0 ∧ g0 ≤ 3 / 10 ∧ 0 < κ ∧ BAbulk 4 4 g0 κ E := by
205:private theorem FinalShape_dom4 {g0 E κ ε : ℝ} (hε : ε ≤ 1) (hb : BAbulk 4 4 g0 κ E) (n : ℕ) :
```
(`FinalShape_bulk4` and `FinalShape_dom4` are `private`: the document names the lemma in prose only. The document says the proof of `Admissible (1/8) (1/10)` is for every `g₀ ∈ (0, 10]`: `FinalShape_cls4_adm (h0 : 0 < g0) (h10 : g0 ≤ 10)`.)

### Acceptance 3: `Thm27` is not restricted to `d = 3`; the `d = 3` lines

```
$ grep -nEi 'T2[0-9]{3}|DECISIONS|paper-delta|ticket|prover|auditor|dispatcher|\bgate\b|pinned|\bowed\b|pending' docs/PAPER-VS-LEAN.md ; echo "grep exit $?"
grep exit 1
$ grep -nEi 'to be merged|registry|not yet|will be' docs/PAPER-VS-LEAN.md ; echo "grep exit $?"
grep exit 1
$ grep -nE 'd = 3' docs/PAPER-VS-LEAN.md | cut -c1-190
110:(`1 − s ≥ 1 − t ≥ g²`, p. 45) of Step 5 of the induction for the block Anderson model at each `d`. The case `d = 3` is `RBM.BA.baThm27L_three`.
139:- `RBM3D/Main/BandTerminal.lean`, §Instances. The size sequence `RBM.Gauss.SizesInst.sz0`: `d = 3`, `L n = 4(n+1)`, `W n = (2(n+1))^5`, `lam n = (2(n+1))^{-6}` (`L = 4`, `W = 32`,
145:- `RBM3D/BA/MAPins.lean`. The class sequence `RBM.Univ.BAInst.S0`: `d = 3`, `L n = 4`, `W n = (2(n+1))^5`, a constant coupling `g₀ ∈ (0, 3/10]` taken from a real-axis solution of (2.32)
148:- `RBM3D/Main/FinalShape.lean`. The ten conjuncts of `final_shape` are applied at the data above (five at `sz0`, five at `S0`; the `d = 3` conjuncts of `Thm27` are `.2 3 le_rfl`), all at
```
All four are about `d = 3` instances or the corollary: line 110 (`baThm27L_three` is the `d = 3` case of `baThm27L_all`), lines 139, 145 (the data `sz0`, `S0` of the `d = 3` examples), line 148 (the `d = 3` conjuncts `.2 3 le_rfl` of the example). None says or implies that Theorem 2.7 is proved only at `d = 3`.

### Acceptance 4: references against the final PDF

`pdftotext` is absent on this machine (`which pdftotext` prints nothing); the per-page text is extracted with PyMuPDF (`pages.py`, 106 pages; PDF page index = printed page, `refs.py`/`chk.py`). `refs.py` compares every `(x.y)`, `Theorem|Lemma|Definition|Remark|Proposition x.y` of the document with `docs/claude-team/tools/paper-labels.tsv` on the pages written on the same line.

```
$ python3 refs.py docs/PAPER-VS-LEAN.md
refs 212 flagged 24
```
Each of the 24 flags was read by hand: a reference on another page than the one cited on the same line (for example "Paper (p. 12, (2.34)): ... (2.11), (2.12)", where (2.11), (2.12) are on p. 8), a reference into another paper ([28, Theorem 2.6], [69, Lemma 4.1], [59, Lemma 3.17], LSY Definition 2.1; not in the tsv), or a page of a proof (Theorems 2.3, 2.4 proved on p. 10; Theorem 2.7 on pp. 11-12, 71-72). The one real mismatch is (2.52); the Itô page was found by `chk.py`/`chk2.py`. The two corrections:

```
$ awk '/PAGE 15=/{f=1} /PAGE 16=/{f=0} f' pdf.txt | grep -n "(2.52)"
21:(2.52)
$ grep -P '\t(2\.52)\t' paper-labels.tsv | cut -f1-4
eq:initial_K	equation	2.52	15
```
The document before: "(2.52) (Definition 2.14, p. 14)"; now: "(Definition 2.14, p. 14; (2.52) is on p. 15)".

```
$ python3 -c ...   (pages of pdf.txt whose text matches 'Itˆo')
pages containing 'Itô': [14, 78]
p. 14: "... By Itˆo's formula, we can derive the following SDE satisfied by the ..."
p. 78: "... The derivation of the loop hierarchy (2.47) by Itˆo's formula does not use the special form of the matrices Eai ..."
```
The document before: "Itô's formula (stated on p. 78)": p. 78 does not state it. Now: "(p. 14; the same derivation is applied to twisted loops on p. 78)".

Page checks of the other page numbers of the document (`chk.py`, whitespace-stripped phrase on the cited page; `chk2.py` for the phrases broken by the extraction):

```
$ python3 chk.py | grep -c '^OK' ; python3 chk.py | grep '^MISS'
47
MISS N=(WL) 7 found on [2]
MISS Sufficientlylarge 8 found on []
MISS ProofofTheorem2.4 11 found on [10]
MISS 2.2Blockrandom 11 found on []
MISS Section8 71 found on [13, 17, 19, 81, 95]
MISS AppendixA.5 86 found on [15, 32, 34]
MISS Itô 78 found on []
MISS Brownianflow 12 found on []
$ python3 chk2.py    (the six MISS phrases, in context)
7  | ...side length WL: Zd W L := J−(WL)/2 + 1, (WL)/2Kd with N = (W · L)d. We partition...
8  | ...the following delocalization estimate holds, provided N is sufficiently large: ... (2.11)
11 | ...2.2. Main results for the block Anderson model. We next define the block Anderson model...
71 | ...8. Extension to the block Anderson model The proof of Theorem 2.7 for the block Anderson model is based on...
86 | ...A.5. Basic properties of K-loops. In this subsection, we collect several basic properties of...
24 | ...bounding the high moments using Gaussian integration by parts and some diagrammatic tools developed in [65, 67]...
```
(Section 2.3 "Stochastic flow", the heading of document §5.1, starts on p. 12 and (2.39), (2.43) are on p. 13: `paper-labels.tsv` lines 64, 69.)

### Narrative

The document on `1a8c2c11` (merged by T2535, before T2533, T2534, T2548, T2551) already used the final names. The edits are the five listed above. Quoted statements are the source statements; the `d = 4` bullet follows the merged `FinalShape.lean` (data `L = 4`, `W_n = (2(n+1))^5`, constant `g₀`, `Admissible (1/8) (1/10)`, nonempty bulk, five conjuncts). Per BDC-C1 the text does not say that a vanishing coupling gives an empty bulk; the only reason given for the constant coupling is that the bulk witness is built at one fixed coupling. Per BDC-C2 the text says all five conjuncts of `Thm27 4` are applied and that BUniv is applied at `k = 1`, `E' = 0`, `bump` on the `d = 4` data.

## (c) Verified Mathlib names

None used (report-only ticket; no Lean written).

## (d) Open issues and paper-delta candidates

1. Item 6 omitted: `grep -rn "IsUnit" RBM3D/BA` finds only private lemmas (`GUEKPrim_isUnit`, `BAKBase_eq_inverse`, `TwistGridWTail_eq_inverse`); no merged public lemma states that `1 − M^{(σ₁,σ₂)}` is invertible on `BAendDom`.
2. `pdftotext` is not installed here; PyMuPDF was used (same page text).
3. No paper-delta candidates (`T2550a`): no Lean/paper statement difference is added; the document is the public list of differences.
4. Merge: report-only ticket, one file (`docs/PAPER-VS-LEAN.md`); the hub brings it by rule (A) steps 3-5 (no new module, so no `RBM3D.lean` change).
